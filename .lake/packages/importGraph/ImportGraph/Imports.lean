/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Command
import Lean.Util.SearchPath
import Lean.Server.GoTo
import Lean.Widget.UserWidget
import ImportGraph.RequiredModules

/-!
# Tools for analyzing imports.

Provides the commands

* `#redundant_imports` which lists any transitively redundant imports in the current module.
* `#min_imports` which attempts to construct a minimal set of imports for the declarations
  in the current file.
  (Must be run at the end of the file. Tactics and macros may result in incorrect output.)
* `#find_home decl` suggests files higher up the import hierarchy to which `decl` could be moved.
-/

open Lean

namespace Lean.Environment

/--
Find the imports of a given module.
-/
def importsOf (env : Environment) (n : Name) : Array Name :=
  if n = env.header.mainModule then
    env.header.imports.map Import.module
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports.map Import.module |>.erase `Init
    | .none => #[]

/--
Construct the import graph of the current file.
-/
partial def importGraph (env : Environment) : NameMap (Array Name) :=
  let main := env.header.mainModule
  let imports := env.header.imports.map Import.module
  imports.foldl (fun m i => process env i m) (({} : NameMap _).insert main imports)
    |>.erase Name.anonymous
where
  process (env) (i) (m) : NameMap (Array Name) :=
    if m.contains i then
      m
    else
      let imports := env.importsOf i
      imports.foldr (fun i m => process env i m) (m.insert i imports)

/--
Return the redundant imports (i.e. those transitively implied by another import)
amongst a candidate list of imports.
-/
partial def findRedundantImports (env : Environment) (imports : Array Name) : NameSet :=
  let run := visit env.importGraph imports
  let (_, seen) := imports.foldl (fun ⟨v, s⟩ n => run v s n) ({}, {})
  seen
where
  visit (Γ) (targets) (visited) (seen) (n) : NameSet × NameSet :=
    if visited.contains n then
      (visited, seen)
    else
      let imports := (Γ.find? n).getD #[]
      let (visited', seen') := imports.foldl (fun ⟨v, s⟩ t => visit Γ targets v s t) (visited, seen)
      (visited'.insert n,
        imports.foldl (fun s t => if targets.contains t then s.insert t else s) seen')

end Lean.Environment

namespace Lean.NameMap

/--
Compute the transitive closure of an import graph.
-/
partial def transitiveClosure (m : NameMap (Array Name)) : NameMap NameSet :=
  m.fold (fun r n i => process r n i) {}
where
  process (r : NameMap NameSet) (n : Name) (i : Array Name) : NameMap NameSet :=
    if r.contains n then
      r
    else
      let r' := i.foldr (fun i r => process r i ((m.find? i).getD #[])) r
      let t := i.foldr
        (fun j s => ((r'.find? j).getD {}).fold NameSet.insert s)
        (RBTree.ofList i.toList)
      r'.insert n t

/--
Compute the transitive reduction of an import graph.

Typical usage is `transitiveReduction (← importGraph)`.
-/
def transitiveReduction (m : NameMap (Array Name)) : NameMap (Array Name) :=
  let c := transitiveClosure m
  m.fold (fun r n a =>
    r.insert n (a.foldr (fun i b => b.filter (fun j => ! ((c.find? i).getD {}).contains j)) a)) {}

/-- Restrict an import graph to only the downstream dependencies of some set of modules. -/
def downstreamOf (m : NameMap (Array Name)) (targets : NameSet) : NameMap (Array Name) :=
  let tc := transitiveClosure m
  let P (n : Name) := targets.contains n || ((tc.find? n).getD {}).any fun j => targets.contains j
  m.fold (init := {}) fun r n i =>
    if P n then
      r.insert n (i.filter P)
    else
      r

/-- Restrict an import graph to only the transitive imports of some set of modules. -/
def upstreamOf (m : NameMap (Array Name)) (targets : NameSet) : NameMap (Array Name) :=
  let tc := transitiveClosure m
  let P (n : Name) := targets.contains n || targets.any fun t => ((tc.find? t).getD {}).contains n
  m.fold (init := {}) fun r n i =>
    if P n then
      r.insert n (i.filter P)
    else
      r

/--
Filter the list of edges `… → node` inside `graph` by the function `filter`.

Any such upstream node `source` where `filter source` returns true will be replaced
by all its upstream nodes. This results in a list of all unfiltered nodes
in the `graph` that either had an edge to `node`
or had an indirect edge to `node` going through filtered nodes.

Will panic if the `node` is not in the `graph`.
-/
partial
def transitiveFilteredUpstream (node : Name) (graph : NameMap (Array Name))
    (filter : Name → Bool) (replacement : Option Name := none):
    List Name :=
  (graph.find! node).toList.flatMap fun source =>
    ( if filter source then
        -- Add the transitive edges going through the filtered node `source`.
        -- If there is a replacement node, add an additional edge `repl → node`.
        match replacement with
        | none => transitiveFilteredUpstream source graph filter
        | some repl => .cons repl <| transitiveFilteredUpstream source graph filter
      -- If the node is not filtered, we leave the edge `source → node` intact.
      else [source]).eraseDups

/--
Filters the `graph` removing all nodes where `filter n` returns false. Additionally,
replace edges from removed nodes by all the transitive edges.

This means there is a path between two nodes in the filtered graph iff there exists
such a path in the original graph.

If the optional `(replacement : Name)` is provided, a corresponding node will be
added together with edges to all nodes which had an incoming edge from any
filtered node.
-/
def filterGraph (graph : NameMap (Array Name)) (filter : Name → Bool)
    (replacement : Option Name := none) : NameMap (Array Name) :=
  -- Create a list of all files imported by any of the filtered files
  -- and remove all imports starting with `Mathlib` to avoid loops.
  let replImports := graph.toList.flatMap
    (fun ⟨n, i⟩ => if filter n then i.toList else [])
    |>.eraseDups |>.filter (¬ Name.isPrefixOf `Mathlib ·) |>.toArray
  let graph := graph.filterMap (fun node edges => if filter node then none else some <|
    -- If the node `node` is not filtered, modify the `edges` going into `node`.
    edges.toList.flatMap (fun source =>
      if filter source then
        transitiveFilteredUpstream source graph filter (replacement := replacement)
      else [source]) |>.eraseDups.toArray)
  -- Add a replacement node if provided.
  match replacement with
  | none => graph
  | some repl => graph.insert repl replImports

end Lean.NameMap

/--
Returns a `List (Name × List Name)` with a key for each module `n` in `amongst`,
whose corresponding value is the list of modules `m` in `amongst` which are transitively imported by `n`,
but no declaration in `n` makes use of a declaration in `m`.
-/
def unusedTransitiveImports (amongst : List Name) (verbose : Bool := false) : CoreM (List (Name × List Name)) := do
  let env ← getEnv
  let transitiveImports := env.importGraph.transitiveClosure
  let transitivelyRequired ← env.transitivelyRequiredModules' amongst verbose
  amongst.mapM fun n => do return (n,
    let unused := (transitiveImports.find? n).getD {} \ (transitivelyRequired.find? n |>.getD {})
    amongst.filter (fun m => unused.contains m))

def Core.withImportModules (modules : Array Name) {α} (f : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => {module := m})) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO
        (ctx := { fileName := "<CoreM>", fileMap := default }) (s := { env := env }) do f

/--
Return the redundant imports (i.e. those transitively implied by another import)
of a specified module (or the current module if `none` is specified).
-/
def redundantImports (n? : Option Name := none) : CoreM NameSet := do
  let env ← getEnv
  let imports := env.importsOf (n?.getD (env.header.mainModule))
  return env.findRedundantImports imports

/--
List the imports in this file which can be removed
because they are transitively implied by another import.
-/
elab "#redundant_imports" : command => do
  let redundant := (← Elab.Command.liftCoreM do redundantImports)
  if redundant.isEmpty then
    logInfo "No transitively redundant imports found."
  else
    logInfo <| "Found the following transitively redundant imports:\n" ++
      m!"{Format.joinSep redundant.toList "\n"}"

/--
Return the names of the modules in which constants used in the current file were defined,
with modules already transitively imported removed.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Lean.Environment.minimalRequiredModules (env : Environment) : Array Name :=
  let required := env.requiredModules.toArray.erase env.header.mainModule
  let redundant := findRedundantImports env required
  required.filter fun n => ¬ redundant.contains n

/--
Try to compute a minimal set of imports for this file,
by analyzing the declarations.

This must be run at the end of the file,
and is not aware of syntax and tactics,
so the results will likely need to be adjusted by hand.
-/
elab "#min_imports" : command => do
  let imports := (← getEnv).minimalRequiredModules.qsort (·.toString < ·.toString)
    |>.toList.map (fun n => "import " ++ n.toString)
  logInfo <| Format.joinSep imports "\n"

-- deprecated since 2024-07-06
elab "#minimize_imports" : command => do
  logWarning m!"'#minimize_imports' is deprecated: please use '#min_imports'"
  Elab.Command.elabCommand (← `(command| #min_imports))

/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
-/
def Lean.Name.findHome (n : Name) (env : Option Environment) : CoreM NameSet := do
  let current? := match env with | some env => env.header.mainModule | _ => default
  let required := (← n.requiredModules).toArray.erase current?
  let imports := (← getEnv).importGraph.transitiveClosure
  let mut candidates : NameSet := {}
  for (n, i) in imports do
    if required.all fun r => n == r || i.contains r then
      candidates := candidates.insert n
  for c in candidates do
    for i in candidates do
      if imports.find? i |>.getD {} |>.contains c then
        candidates := candidates.erase i
  return candidates

open Server in
/-- Tries to resolve the module `modName` to a source file URI.
This has to be done in the Lean server
since the `Environment` does not keep track of source URIs. -/
@[server_rpc_method]
def getModuleUri (modName : Name) : RequestM (RequestTask Lsp.DocumentUri) :=
  RequestM.asTask do
    let some uri ← documentUriFromModule? modName
      | throw $ RequestError.invalidParams s!"couldn't find URI for module '{modName}'"
    return uri

structure GoToModuleLinkProps where
  modName : Name
  deriving Server.RpcEncodable

/-- When clicked, this widget component jumps to the source of the module `modName`,
assuming a source URI can be found for the module. -/
@[widget_module]
def GoToModuleLink : Widget.Module where
  javascript := "
    import * as React from 'react'
    import { EditorContext, useRpcSession } from '@leanprover/infoview'

    export default function(props) {
      const ec = React.useContext(EditorContext)
      const rs = useRpcSession()
      return React.createElement('a',
        {
          className: 'link pointer dim',
          onClick: async () => {
            try {
              const uri = await rs.call('getModuleUri', props.modName)
              ec.revealPosition({ uri, line: 0, character: 0 })
            } catch {}
          }
        },
        props.modName)
    }
  "

open Elab Command in
/--
Find locations as high as possible in the import hierarchy
where the named declaration could live.
Using `#find_home!` will forcefully remove the current file.
Note that this works best if used in a file with `import Mathlib`.

The current file could still be the only suggestion, even using `#find_home! lemma`.
The reason is that `#find_home!` scans the import graph below the current file,
selects all the files containing declarations appearing in `lemma`, excluding
the current file itself and looks for all least upper bounds of such files.

For a simple example, if `lemma` is in a file importing only `A.lean` and `B.lean` and
uses one lemma from each, then `#find_home! lemma` returns the current file.
-/
elab "#find_home" bang:"!"? n:ident : command => do
  let stx ← getRef
  let mut homes : Array MessageData := #[]
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env? ← bang.mapM fun _ => getEnv
  for modName in (← Elab.Command.liftCoreM do n.findHome env?) do
    let p : GoToModuleLinkProps := { modName }
    homes := homes.push $ .ofWidget
      (← liftCoreM $ Widget.WidgetInstance.ofHash
        GoToModuleLink.javascriptHash $
        Server.RpcEncodable.rpcEncode p)
      (toString modName)
  logInfoAt stx[0] m!"{homes}"
