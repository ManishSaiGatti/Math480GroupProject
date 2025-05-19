import Mathlib

-- definition of a simple graph: a adj function from the vertex set to itself
#check SimpleGraph --SimpleGraph.{u} (V : type u) : Type u

-- abbreviation of def/theorems of the set of edges of a simple graph
#check SimpleGraph.edgeSet /-
SimpleGraph.edgeSet.{u} {V : Type u}
(G : SimpleGraph V) : Set (Sym2 V)
-/

-- original theorem referring to edge set
#check SimpleGraph.mem_edgeSet /-
SimpleGraph.mem_edgeSet.{u}
{V : Type u} (G : SimpleGraph V) {v w : V} :
s(v, w) ∈ G.edgeSet ↔ G.Adj v w
-/

-- the set of edges incident to a given vertex
#check SimpleGraph.incidenceSet /-
SimpleGraph.incidenceSet.{u} {V : Type u}
(G : SimpleGraph V) (v : V) : Set (Sym2 V)
-/

-- theorem that states the number of edges incident to a vertex equals the number of vertices neighbor to that vertex
#check SimpleGraph.incidenceSetEquivNeighborSet /-
SimpleGraph.incidenceSetEquivNeighborSet.{u}
{V : Type u} (G : SimpleGraph V) [DecidableEq V] (v : V) :
  ↑(G.incidenceSet v) ≃ ↑(G.neighborSet v)
-/

-- a proper VERTEX coloring of a simple graph
#check SimpleGraph.Coloring.mk/-
SimpleGraph.Coloring.mk.{u, u_1} {V : Type u}
{G : SimpleGraph V} {α : Type u_1} (color : V → α)
  (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) : G.Coloring α
-/

-- checking whether a graph is vertex colorable by at most n colors
#check SimpleGraph.Colorable/-
SimpleGraph.Colorable.{u} {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop
-/

-- theorem of removing a set of edges from a simple graph
#check SimpleGraph.edgeSet_sdiff /-
SimpleGraph.edgeSet_sdiff.{u} {V : Type u}
(G₁ G₂ : SimpleGraph V) : (G₁ \ G₂).edgeSet
= G₁.edgeSet \ G₂.edgeSet
-/

/-- A finite simple graph is a simple graph with a finite vertex set. -/
structure FiniteSimpleGraph (V : Type u) extends SimpleGraph V where
  is_finite : Finite V

/-- An edge coloring of a simple graph G assigns a color to each edge in G.edgeSet. -/
structure SimpleGraph.EdgeColoring {V : Type u} (G : SimpleGraph V) (α : Type v) where
  color : G.edgeSet → α

/-- A proper edge coloring is one where no two adjacent edges have the same color. -/
def SimpleGraph.EdgeColoring.IsProper {V : Type u} {G : SimpleGraph V}
    {α : Type v} (coloring : G.EdgeColoring α) : Prop :=
  ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
    (∃ v : V, v ∈ e₁.val ∧ v ∈ e₂.val) → coloring.color e₁ ≠ coloring.color e₂

/-- A proper edge coloring constructor with proof of validity. -/
def SimpleGraph.EdgeColoring.mk_proper {V : Type u} {G : SimpleGraph V}
    {α : Type v} (color : G.edgeSet → α)
    (valid : ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
      (∃ v : V, v ∈ e₁.val ∧ v ∈ e₂.val) → color e₁ ≠ color e₂) :
    G.EdgeColoring α :=
  { color := color }


/-- A graph is edge colorable with n colors if there exists a proper edge coloring
    using at most n colors. -/
def SimpleGraph.EdgeColorable {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∃ coloring : G.EdgeColoring (Fin n), coloring.IsProper


/-- Vizing's theorem: The proper edge coloring of a simple graph is less than or equal to Δ+1,
    where Δ is the maximum degree of the graph. -/
theorem SimpleGraph.vizing_theorem {V : Type u}
    (G : FiniteSimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj] :
    ∃ n : ℕ, n ≤ G.maxDegree + 1 ∧ G.EdgeColorable n := by
    use G.maxDegree + 1
    sorry


/-- Another way to formalize vizings theorem (via Jarod)-/
theorem SimpleGraph.vizing_theorem2 {V : Type u}
    (G : FiniteSimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj] :
    G.EdgeColorable (G.maxDegree + 1) := by
    --use G.maxDegree + 1
    -- Base case: if G has no edges then it is trivially colorable with 0 colors
    let n := G.maxDegree + 1
    have base_case : n = 0 → G.edgeSet = ∅ := by
      intro h
      sorry

    -- Inductive step: if G has less than n edges, we can color it with d+1 colors, where
    -- d is the maximum degree of G
    have induction_hypothesis : ∀ (H : FiniteSimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel H.Adj],
      Fintype.card H.edgeSet < Fintype.card G.edgeSet → H.EdgeColorable (H.maxDegree + 1) := by
      sorry
