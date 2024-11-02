import Mathlib

import ErdosStoneSimonovits.Degree

namespace SimpleGraph

variable {V α β : Type*} {G : SimpleGraph V} {s t : Set V} {x : V}

section Restrict

/-- The restriction of a simple graph to the *edges* with vertices in the set
`s`, deleting all edges incident to vertices outside the set. -/
abbrev restrict (s : Set V) (G : SimpleGraph V) :
  SimpleGraph V := (G.induce s).spanningCoe

theorem restrict_adj :
    (G.restrict s).Adj v w ↔ G.Adj v w ∧ v ∈ s ∧ w ∈ s := by
  simp_rw [map_adj, comap_adj, Function.Embedding.coe_subtype]
  constructor
  . intro ⟨x, y, hadj, hx, hy⟩
    rw [hx, hy] at hadj
    refine ⟨hadj, ?_, ?_⟩
    . rw [←hx]
      exact x.prop
    . rw [←hy]
      exact y.prop
  . intro ⟨hadj, hv, hw⟩
    use ⟨v, hv⟩, ⟨w, hw⟩, hadj

instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] :
    DecidableRel (G.restrict s).Adj := by
  intro _ _
  rw [restrict_adj]
  infer_instance

/-- The simple graph restricted on `Set.univ` is equal to the original simple
graph. -/
theorem restrict_univ_eq (G : SimpleGraph V) :
    G.restrict Set.univ = G := by
  ext; simp

/-- The simple graph `G` restricted on `G.support` is equal to the original
simple graph `G`. -/
theorem restrict_support_eq (G : SimpleGraph V) :
    G.restrict G.support = G := by
  ext v w
  rw [restrict_adj]
  exact ⟨fun ⟨h, _, _⟩ ↦ h, fun h ↦ ⟨h, ⟨w, h⟩, ⟨v, h.symm⟩⟩⟩

instance [Fintype V] [DecidableRel G.Adj] : DecidablePred (· ∈ G.support) := by
  unfold SimpleGraph.support Rel.dom
  infer_instance

lemma card_edgeFinset_restrict_support_eq [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.restrict G.support).edgeFinset.card = G.edgeFinset.card := by
  simp_rw [Set.toFinset_card, restrict_support_eq]

lemma degree_restrict_support_eq [Fintype V] [DecidableRel G.Adj] (v : V) :
    (G.restrict G.support).degree v = G.degree v := by
  simp_rw [←card_neighborSet_eq_degree]
  apply Fintype.card_congr
  rw [restrict_support_eq]

theorem restrict_support_subset (s : Set V) :
    (G.restrict s).support ⊆ s := by
  intro _
  rw [mem_support, exists_imp]
  intro _ h
  rw [restrict_adj] at h
  exact h.2.1

/-- The simple graphs restricted on `s ⊆ t` are subgraphs. -/
theorem restrict_le_of_subset (h : s ⊆ t):
    G.restrict s ≤ G.restrict t := by
  intro _ _ hadj
  rw [restrict_adj] at hadj ⊢
  exact ⟨hadj.1, h hadj.2.1, h hadj.2.2⟩

theorem restrict_le (s : Set V) :
    G.restrict s ≤ G := by
  conv_rhs =>
    rw [←restrict_univ_eq G]
  exact restrict_le_of_subset (Set.subset_univ s)

/-- The simple graphs restricted on `Disjoint s t` are disjoint. -/
theorem disjoint_restrict (h : Disjoint s t) :
    Disjoint (G.restrict s) (G.restrict t) := by
  rw [←disjoint_edgeSet, Set.disjoint_iff_inter_eq_empty, ←edgeSet_inf,
    edgeSet_eq_empty]
  ext
  rw [inf_adj, restrict_adj, restrict_adj, bot_adj, iff_false]
  push_neg
  rw [and_imp, and_imp]
  intro _ _ hw _ _
  rw [Set.disjoint_left] at h
  exact h hw

/-- The neighbor sets of restricted subgraphs are equivalent to the neighbor
sets of induced subgraphs. -/
def Restrict.mapNeighborSet (v : s) :
    (G.restrict s).neighborSet v ≃ (G.induce s).neighborSet v where
  toFun := by
    intro ⟨w, h⟩
    rw [mem_neighborSet, restrict_adj] at h
    use ⟨w, h.2.2⟩
    rw [mem_neighborSet, comap_adj, Function.Embedding.coe_subtype]
    exact h.1
  invFun := by
    intro ⟨w, h⟩
    rw [mem_neighborSet, comap_adj, Function.Embedding.coe_subtype] at h
    use w.val
    rw [mem_neighborSet, restrict_adj]
    exact ⟨h, v.prop, w.prop⟩
  left_inv w := by simp
  right_inv w := by simp

/-- The degree of vertices in restricted subgraphs are equal to the degree of
vertices in induced subgraphs. -/
theorem degree_restrict_eq_induce
    [Fintype V] [DecidableRel G.Adj] [DecidablePred (· ∈ s)] (v : s) :
    (G.restrict s).degree v = (G.induce s).degree v := by
  simp_rw [←card_neighborSet_eq_degree]
  exact Fintype.card_congr (Restrict.mapNeighborSet v)

/-- The number of edges in restricted subgraphs are equal to the number of
edges in induced subgraphs. -/
theorem card_edgeFinset_restrict_eq_induce [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)] :
    (G.restrict s).edgeFinset.card = (G.induce s).edgeFinset.card := by
  rw [←Nat.mul_right_inj two_ne_zero]
  simp_rw [←sum_degrees_eq_twice_card_edges,
    ←Finset.sum_add_sum_compl s.toFinset, ←Finset.sum_set_coe,
    degree_restrict_eq_induce, add_right_eq_self]
  apply Finset.sum_eq_zero
  intro _ h
  rw [degree_eq_zero_iff]
  apply Set.not_mem_subset (restrict_support_subset s)
  rwa [←Set.toFinset_compl, Set.mem_toFinset, Set.mem_compl_iff] at h

lemma card_edgeFinset_induce_support_eq
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (G.induce G.support).edgeFinset.card = G.edgeFinset.card := by
  rw [←card_edgeFinset_restrict_eq_induce]
  exact card_edgeFinset_restrict_support_eq G

/-- Any simple graph with `n` vertices in its support has at most `n.choose 2`
edges. -/
theorem card_edgeFinset_le_card_support_choose_two
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (Fintype.card G.support).choose 2 := by
  rw [←card_edgeFinset_induce_support_eq]
  exact card_edgeFinset_le_card_choose_two

/-- The restricted subgraph to the set `t` of the restricted subgraph to the
set `s` is equal to the restricted subgraph to the intersection `s ∩ t`. -/
theorem restrict_restrict :
    (G.restrict s).restrict t = G.restrict (s ∩ t) := by
  ext v w
  simp_rw [restrict_adj, Set.mem_inter_iff]
  exact ⟨fun ⟨⟨h, hs⟩, ht⟩ ↦ ⟨h, ⟨hs.1, ht.1⟩, hs.2, ht.2⟩,
    fun ⟨h, hv, hw⟩ ↦ ⟨⟨h, ⟨hv.1, hw.1⟩⟩, hv.2, hw.2⟩⟩

/-- The induced subgraph on the set `t ⊆ s` of the restricted subgraph to the
set `s` is equal to the induced subgraph on the set `t`. -/
theorem induce_restrict (h : t ⊆ s) :
    (G.restrict s).induce t = G.induce t := by
  ext v w
  simp_rw [comap_adj, Function.Embedding.coe_subtype, restrict_adj]
  exact ⟨fun ⟨hadj, _, _⟩ ↦ hadj, fun hadj ↦ ⟨hadj, h v.prop, h w.prop⟩⟩

lemma map_support_eq_image (G : SimpleGraph α) (f : α ↪ β) :
    (G.map f).support = f '' G.support := by
  ext; simp_rw [Set.mem_image, mem_support, map_adj]
  exact ⟨fun ⟨_, v, w, h, hv, _⟩ ↦ ⟨v, ⟨w, h⟩, hv⟩,
    fun ⟨v, ⟨w, h⟩, hv⟩ ↦ ⟨f w, v, w, h, hv, by rfl⟩⟩

noncomputable def Iso.mapInduceSupport
    (G : SimpleGraph α) [DecidableRel G.Adj] (f : α ↪ β) :
    (G.induce G.support) ≃g (G.map f).induce (f '' G.support) where
  toFun := Equiv.Set.image f G.support f.injective
  invFun := Equiv.symm (Equiv.Set.image f G.support f.injective)
  left_inv := by
    intro _; simp
  right_inv := by
    intro _; simp
  map_rel_iff' := by
    intro _ _; simp [Equiv.Set.univ]

/-- The number of edges in a mapped simple graph is equal to the number of
edges in the original simple graph. -/
theorem card_edgeFinset_map [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (G : SimpleGraph α) [DecidableRel G.Adj] (f : α ↪ β) :
    (G.map f).edgeFinset.card = G.edgeFinset.card := by
  conv_lhs =>
    rw [←card_edgeFinset_induce_support_eq]
  conv_rhs =>
    rw [←card_edgeFinset_induce_support_eq]
  trans ((G.map f).induce (f '' G.support)).edgeFinset.card
  all_goals apply Iso.card_edgeFinset_eq
  . rw [map_support_eq_image]
  . exact (Iso.mapInduceSupport G f).symm

end Restrict

section DeleteIncidenceSet

/-- Delete all edges from the incidence set of a vertex. -/
abbrev deleteIncidenceSet (x : V) (G : SimpleGraph V) :
  SimpleGraph V := G.deleteEdges (G.incidenceSet x)

/-- Deleting the edges from the incidence set of a vertex restricts the edges
to the set `{x}ᶜ`. -/
lemma deleteIncidenceSet_eq_restrict_compl_singleton
    (G : SimpleGraph V) (x : V) :
    G.deleteIncidenceSet x = G.restrict {x}ᶜ := by
  ext v w
  simp_rw [restrict_adj, Set.mem_compl_singleton_iff, deleteIncidenceSet,
    deleteEdges, sdiff_adj, fromEdgeSet_adj, incidenceSet, Set.mem_setOf_eq,
    mem_edgeSet, Sym2.mem_iff]
  push_neg
  rw [or_iff_not_and_not]
  constructor
  . intro ⟨h, hvw⟩
    refine ⟨h, ?_⟩
    by_contra nh
    absurd h.ne
    simp_rw [ne_comm] at nh
    exact hvw ⟨h, nh⟩
  . intro ⟨h, hv, hw⟩
    refine ⟨h, ?_⟩
    intro ⟨_, nh⟩
    absurd nh
    exact ⟨hv.symm, hw.symm⟩

theorem deleteIncidenceSet_adj :
    (G.deleteIncidenceSet x).Adj v w ↔ G.Adj v w ∧ v ≠ x ∧ w ≠ x := by
  simp_rw [deleteIncidenceSet_eq_restrict_compl_singleton G x,
    restrict_adj, Set.mem_compl_singleton_iff]

/-- Deleting the edges from the incidence set of a vertex restricts the edges
to the set `G.support \ {x}`. -/
lemma deleteIncidenceSet_eq_restrict_support_diff_singleton (x : V) :
    G.deleteIncidenceSet x = G.restrict (G.support \ {x}) := by
  ext v w
  simp_rw [deleteIncidenceSet_adj, restrict_adj, Set.mem_diff,
    ←Set.mem_compl_iff, Set.mem_compl_singleton_iff, mem_support]
  exact ⟨fun ⟨h, hv, hw⟩ ↦ ⟨h, ⟨⟨w, h⟩, hv⟩, ⟨⟨v, h.symm⟩, hw⟩⟩,
    fun ⟨h, ⟨_, hv⟩, ⟨_, hw⟩⟩ ↦ ⟨h, hv, hw⟩⟩

/-- Deleting the edges from the incidence set of a vertex deletes the vertex
from the support. -/
theorem deleteIncidenceSet_support_subset
    (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support ⊆ G.support \ {x} := by
  rw [deleteIncidenceSet_eq_restrict_support_diff_singleton]
  exact restrict_support_subset _

theorem deleteIncidenceSet_restrict_of_not_mem
    (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).restrict s = G.restrict s := by
  have h_inter_eq : {x}ᶜ ∩ s = s := by
    rwa [←Set.subset_compl_singleton_iff, ←Set.inter_eq_right] at h
  rw [deleteIncidenceSet_eq_restrict_compl_singleton, restrict_restrict,
    h_inter_eq]

theorem deleteIncidenceSet_induce_of_not_mem
    (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  rw [deleteIncidenceSet_eq_restrict_compl_singleton, induce_restrict]
  rwa [←Set.subset_compl_singleton_iff] at h

lemma card_fromEdgeSet_incidenceSet
    [Fintype V] [DecidableEq V] (x : V) [DecidableRel G.Adj] :
    (fromEdgeSet (G.incidenceSet x)).edgeFinset.card = G.degree x := by
  have h : (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
    rw [edgeSet_fromEdgeSet, sdiff_eq_left,
      ←Set.subset_compl_iff_disjoint_right, Set.compl_setOf]
    exact (incidenceSet_subset G x).trans (edgeSet_subset_setOf_not_isDiag G)
  simp_rw [Set.toFinset_card, h, card_incidenceSet_eq_degree]

variable [Fintype V] [DecidableEq V]

instance {G : SimpleGraph V} [DecidableRel G.Adj] :
    DecidableRel (G.deleteIncidenceSet x).Adj := by
  rw [deleteIncidenceSet_eq_restrict_compl_singleton G x]
  infer_instance

/-- Deleting the incidence set of the vertex `x` from `G` deletes exactly
`G.degree x` edges from `G`. -/
theorem card_edgeFinset_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset.card
      = G.edgeFinset.card-G.degree x := by
  have h : (fromEdgeSet (G.incidenceSet x)).edgeFinset ⊆ G.edgeFinset := by
    rw [Set.toFinset_subset_toFinset, edgeSet_fromEdgeSet]
    exact Set.diff_subset.trans (incidenceSet_subset G x)
  simp_rw [←card_fromEdgeSet_incidenceSet, ←Finset.card_sdiff h,
    ←edgeFinset_sdiff, Set.toFinset_card, deleteEdges]
  convert rfl

theorem card_edgeFinset_deleteIncidenceSet_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset.card ≤ G.edgeFinset.card := by
  rw [card_edgeFinset_deleteIncidenceSet G x]
  exact Nat.sub_le _ _

theorem edgeFinset_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  ext e
  rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_diff, Finset.mem_filter,
    Set.mem_toFinset, and_congr_right_iff]
  intro h
  let e' : G.edgeSet := ⟨e, h⟩
  rw [show e = e'.val by rfl, edge_mem_incidenceSet_iff]

/-- Deleting the incidence set of the vertex `x` from `G` deletes at most one
vertex from the support of `G`. -/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x ∈ G.support) :
    Fintype.card (G.deleteIncidenceSet x).support
      ≤ Fintype.card G.support - 1 := by
  rw [←Set.singleton_subset_iff, ←Set.toFinset_subset_toFinset] at hx
  simp_rw [←Set.card_singleton x, ←Set.toFinset_card,
    ←Finset.card_sdiff hx, ←Set.toFinset_diff]
  apply Finset.card_le_card
  rw [Set.toFinset_subset_toFinset,
    deleteIncidenceSet_eq_restrict_support_diff_singleton x]
  exact restrict_support_subset _

end DeleteIncidenceSet
