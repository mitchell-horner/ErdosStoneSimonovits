import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Finite

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section DeleteEdges

variable {G} {s : Set (Sym2 V)}

instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] :
    DecidableRel (G.deleteEdges s).Adj := by
  intro v w
  rw [deleteEdges_adj]
  infer_instance

end DeleteEdges

section DeleteIncidenceSet

/-- Given a vertex `x`, remove the edges incident to `x` from the edge set. -/
abbrev deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (G.incidenceSet x)

lemma deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} :
    (G.deleteIncidenceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ ≠ x ∧ v₂ ≠ x := by
  rw [deleteEdges_adj, mk'_mem_incidenceSet_iff]
  tauto

lemma deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x ≤ G :=
  deleteEdges_le (G.incidenceSet x)

lemma edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) :
    (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, ← Set.subset_compl_iff_disjoint_right, Set.compl_setOf]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_setOf_not_isDiag

/-- The edge set of `G.deleteIncidenceSet x` is the edge set of `G` set difference the incidence
set of the vertex `x`. -/
theorem edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ (G.incidenceSet x) := by
  simp_rw [deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

/-- The support of `G.deleteIncidenceSet x` is a subset of the support of `G` set difference the
singleton set `{x}`. -/
theorem deleteIncidenceSet_support_subset (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support ⊆ G.support \ {x} :=
  fun _ ↦ by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

/-- If the vertex `x` is not in the set `s`, then the induced subgraph in `G.deleteIncidenceSet x`
by `s` is equal to the induced subgraph in `G` by `s`. -/
theorem deleteIncidenceSet_induce_of_not_mem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨v₁.prop.ne_of_not_mem h, v₂.prop.ne_of_not_mem h⟩

variable [Fintype V] [DecidableEq V]

/-- Deleting the incidence set of the vertex `x` retains the same number of edges as in the induced
subgraph of the vertices `{x}ᶜ`. -/
theorem card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset := by
  have h_not_mem : x ∉ ({x}ᶜ : Set V) := Set.not_mem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [Set.toFinset_card,
    ← G.deleteIncidenceSet_induce_of_not_mem h_not_mem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact deleteIncidenceSet_support_subset G x
  · rw [Set.compl_eq_univ_diff]
    exact Set.diff_subset_diff_left (Set.subset_univ G.support)

/-- The finite edge set of `G.deleteIncidenceSet x` is the finite edge set of the simple graph `G`
set difference the finite incidence set of the vertex `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ (G.incidenceFinset x) := by
  rw [incidenceFinset, ← Set.toFinset_diff, Set.toFinset_inj]
  exact G.edgeSet_deleteIncidenceSet x

/-- Deleting the incident set of the vertex `x` deletes exactly `G.degree x` edges from the edge
set of the simple graph `G`. -/
theorem card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset-G.degree x := by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

/-- Deleting the incident set of the vertex `x` is equivalent to filtering the edges of the simple
graph `G` that do not contain `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff, sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset, Set.mem_toFinset, incidenceSet, Set.mem_setOf_eq, not_and, Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

/-- The support of `G.deleteIncidenceSet x` is at most `1` less than the support of the simple
graph `G`. -/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x ∈ G.support) :
    card (G.deleteIncidenceSet x).support ≤ card G.support - 1 := by
  rw [← Set.singleton_subset_iff, ← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff hx, ← Set.toFinset_diff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.deleteIncidenceSet_support_subset x

end DeleteIncidenceSet

end SimpleGraph
