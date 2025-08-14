import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Basic
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Maps
import ErdosStoneSimonovits.Data.Sym.Sym2

open Finset Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section EdgeFinset

variable {G} [Fintype G.edgeSet]

/-- The size of the finite set corresponding to an edge is `2`. -/
theorem card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) :
    (e : Sym2 V).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

end EdgeFinset

section FiniteAt

variable (v) [Fintype (G.neighborSet v)]

theorem incidenceFinset_subset [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v ⊆ G.edgeFinset := by
  rw [incidenceFinset, Set.toFinset_subset_toFinset]
  exact G.incidenceSet_subset v

theorem degree_pos_iff_mem_support : 0 < G.degree v ↔ v ∈ G.support := by
  rw [G.degree_pos_iff_exists_adj v, mem_support]

theorem degree_eq_zero_iff_not_mem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]

/-- The degree of a vertex is at most the number of edges. -/
theorem degree_le_card_edgeFinset [DecidableEq V] [Fintype G.edgeSet] :
    G.degree v ≤ #G.edgeFinset := by
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

end FiniteAt

section Finite

variable [Fintype V]

/-- In a nonempty graph, the minimal degree is less than the number of vertices. -/
theorem minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V := by
  obtain ⟨v, hδ⟩ := G.exists_minimal_degree_vertex
  rw [hδ, ← card_neighborFinset_eq_degree, ← card_univ]
  have h : v ∉ G.neighborFinset v := by
    rw [mem_neighborFinset]
    exact G.loopless v
  contrapose! h
  rw [eq_of_subset_of_card_le (subset_univ _) h]
  exact mem_univ v

end Finite

section Support

variable {s : Set V} [DecidablePred (· ∈ s)] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma edgeFinset_subset_sym2_of_support_subset (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  simp_rw [subset_iff, Sym2.forall,
    mem_edgeFinset, mem_edgeSet, mk_mem_sym2_iff, Set.mem_toFinset]
  intro _ _ hadj
  exact ⟨h ⟨_, hadj⟩, h ⟨_, hadj.symm⟩⟩

instance : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })

variable [DecidableEq V]

theorem map_edgeFinset_induce :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map
      = G.edgeFinset ∩ s.toFinset.sym2 := by
  simp_rw [Finset.ext_iff, Sym2.forall, mem_inter, mk_mem_sym2_iff, mem_map, Sym2.exists,
    Set.mem_toFinset, mem_edgeSet, comap_adj, Embedding.sym2Map_apply, Embedding.coe_subtype,
    Sym2.map_pair_eq, Sym2.eq_iff]
  intro v w
  constructor
  · rintro ⟨x, y, hadj, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
    all_goals rw [← hv, ← hw]
    · exact ⟨hadj, x.prop, y.prop⟩
    · exact ⟨hadj.symm, y.prop, x.prop⟩
  · intro ⟨hadj, hv, hw⟩
    use ⟨v, hv⟩, ⟨w, hw⟩, hadj
    tauto

theorem map_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map = G.edgeFinset := by
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
theorem card_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [← map_edgeFinset_induce_of_support_subset h, card_map]

theorem card_edgeFinset_induce_support :
    #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl

theorem map_neighborFinset_induce (v : s) :
    ((G.induce s).neighborFinset v).map (.subtype s)
      = G.neighborFinset v ∩ s.toFinset := by
  ext; simp [Set.mem_def]

theorem map_neighborFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    ((G.induce s).neighborFinset v).map (.subtype s) = G.neighborFinset v := by
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

/-- If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the vertex in the
induced subgraph of `s` is the same as in `G`. -/
theorem degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    (G.induce s).degree v = G.degree v := by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

/-- If the support of the simple graph `G` is a subset of the set `s`, then the degree of vertices
in the induced subgraph of `s` are the same as in `G`. -/
theorem degree_induce_of_support_subset (h : G.support ⊆ s) (v : s) :
    (G.induce s).degree v = G.degree v :=
  degree_induce_of_neighborSet_subset <| (G.neighborSet_subset_support v).trans h

@[simp]
theorem degree_induce_support (v : G.support) :
    (G.induce G.support).degree v = G.degree v :=
  degree_induce_of_support_subset subset_rfl v

end Support

section Map

variable [Fintype V] [DecidableEq V] {W : Type*} [Fintype W] [DecidableEq W]

@[simp]
theorem card_edgeFinset_map (G : SimpleGraph V) [DecidableRel G.Adj] (f : V ↪ W) :
    #(G.map f).edgeFinset = #G.edgeFinset := by
  conv_lhs =>
    rw [← card_edgeFinset_induce_support]
  conv_rhs =>
    rw [← card_edgeFinset_induce_support]
  apply Iso.card_edgeFinset_eq
  rw [support_map_eq_image]
  apply Iso.symm; use Equiv.Set.image f G.support f.injective, by simp

end Map

end SimpleGraph
