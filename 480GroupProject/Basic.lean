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

instance : Coe (FiniteSimpleGraph V) (SimpleGraph V) := ⟨FiniteSimpleGraph.toSimpleGraph⟩

/-- An edge coloring of a simple graph G assigns a color to each edge in G.edgeSet. -/
structure SimpleGraph.EdgeColoring {V : Type u} (G : SimpleGraph V) (α : Type v) where
  color : G.edgeSet → α

/-- A proper edge coloring is one where no two adjacent edges have the same color. -/
def SimpleGraph.EdgeColoring.IsProper {V : Type u} {G : SimpleGraph V}
    {α : Type v} (coloring : G.EdgeColoring α) : Prop :=
  ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
    (∃ v : V, v ∈ e₁.val ∧ v ∈ e₂.val) → coloring.color e₁ ≠ coloring.color e₂

/- A proper edge coloring constructor with proof of validity.
def SimpleGraph.EdgeColoring.mk_proper {V : Type u} {G : SimpleGraph V}
    {α : Type v} (color : G.edgeSet → α)
    (valid : ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
      (∃ v : V, v ∈ e₁.val ∧ v ∈ e₂.val) → color e₁ ≠ color e₂) :
    G.EdgeColoring α :=
  { color := color }
-/

/-- A graph is edge colorable with n colors if there exists a proper edge coloring
    using at most n colors. -/
def SimpleGraph.EdgeColorable {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∃ coloring : G.EdgeColoring (Fin n), coloring.IsProper

-- Vizing's theorem and proof
theorem SimpleGraph.vizing_theorem3 {V : Type u}
    (G : FiniteSimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj] :
    G.EdgeColorable (G.maxDegree + 1) := by
  -- We will use induction on the number of edges in G
    induction' h: Fintype.card G.edgeSet with n ih
    -- Base case: if G has no edges then it is trivially colorable with 0 colors
    case zero =>
      unfold SimpleGraph.EdgeColorable
      -- create a coloring that assigns color 1 to all edges
      let myColoring : G.EdgeColoring (Fin (G.maxDegree+1)) := SimpleGraph.EdgeColoring.mk (fun e => 1)
      use myColoring
      -- prove that this coloring is proper
      unfold SimpleGraph.EdgeColoring.IsProper
      intros e₁ e₂ hne he
      -- proof by contradiction
      exfalso
      -- if the edge set is empty, then there are no edges to color
      have h_no_elements : ¬ Nonempty G.edgeSet := by
        rw [← Fintype.card_pos_iff]
        simp [h]
      -- this means that there are no edges e₁ and e₂
      have h_nonempty : Nonempty G.edgeSet := by
        use e₁
        exact Subtype.coe_prop e₁
      contradiction
    -- Inductive step: assume the theorem holds for graphs with n edges
    -- and show it holds for graphs with n+1 edges
    case succ n ih =>
      -- Pick an edge e₀ from G.edgeSet
      have h_card_pos : 0 < Fintype.card G.edgeSet := by
        rw [h]
        exact Nat.zero_lt_succ n

      obtain ⟨e₀, _⟩ := Fintype.card_pos_iff.mp h_card_pos

      -- Remove e₀ from G to get a new graph G'
      let G' := G.deleteEdges {e₀}

      -- Show that G' has exactly n edges
      have h_card_G' : Fintype.card G'.edgeSet = n := by
        have h_edge_set_eq : G'.edgeSet = G.edgeSet \ {e₀} := by
          unfold G'
          simp [SimpleGraph.edgeSet_sdiff, SimpleGraph.deleteEdges]
        sorry

      -- By the inductive hypothesis, G' is edge colorable with at most G'.maxDegree + 1 colors
      have ih_G' : G'.EdgeColorable (G'.maxDegree + 1) := by
        sorry

      rcases ih_G' with ⟨coloring', h_proper'⟩

      -- The max degree of G' is at most the max degree of G
      have h_max_degree : G'.maxDegree ≤ G.maxDegree := by
        sorry

      -- Since the max degree of G' is at most the max degree of G,
      -- it follows that G' is edge colorable with at most G.maxDegree + 1 colors
      have G'_colorable : G'.EdgeColorable (G.maxDegree + 1) := by
        sorry -- Use monotonicity of edge coloring and h_max_degree_bound

      -- Get the proper coloring of G'
      obtain ⟨coloring', h_proper'⟩ := G'_colorable

      -- Collect colors used by edges incident to u in G'
      let colors_at_u : Finset (Fin (G.maxDegree + 1)) := sorry

      -- Collect colors used by edges incident to v in G'
      let colors_at_v : Finset (Fin (G.maxDegree + 1)) := sorry

      -- Since degrees are bounded by max degree, and we have max_degree + 1 colors available
      have h_total_colors : (colors_at_u ∪ colors_at_v).card ≤ 2 * G.maxDegree := by
        sorry

      -- We have max_degree + 1 colors, but up to 2 * max_degree may be forbidden
    -- Since max_degree + 1 ≤ 2 * max_degree when max_degree ≥ 1,
    -- naive counting doesn't guarantee an available color
    -- This is why we need alternating path technique

      by_cases h_available : ∃ c : Fin (G.maxDegree + 1), c ∉ colors_at_u ∧ c ∉ colors_at_v

      -- Case 1: There exists an available color for edge e₀
      case pos =>
        obtain ⟨available_color, hc_not_u, hc_not_v⟩ := h_available

        -- Extend the coloring to include e₀ with the available color
        let extended_coloring : G.EdgeColoring (Fin (G.maxDegree + 1)) := by
          sorry -- Define coloring that agrees with coloring' on G'.edgeSet and assigns available_color to e₀

        use extended_coloring

        -- Prove that the extended coloring is proper
        unfold SimpleGraph.EdgeColoring.IsProper
        intros e₁ e₂ hne h_adjacent
        sorry -- Show that the extension preserves properness

      -- Case 2: No color is available (all colors appear at u or v) -> This is where to use the alternating path argument
      case neg =>
        sorry
