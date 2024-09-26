import Mathlib

import ErdosStoneSimonovits.Restrict

open BigOperators

namespace SimpleGraph

variable {V : Type*} {G G₁ G₂ : SimpleGraph V} {s t : Set V}

section IsBipartite

/-- A simple graph `G` satisfies `IsBipartite G s t` if the vertices that form
edges in `G` are divided into two disjoint and independent sets `s` and `t`,
that is, every edge in `G` connects a vertex in `s` to a vertex in `t`. -/
abbrev IsBipartite (G : SimpleGraph V) (s t : Set V) :=
  Disjoint s t ∧ ∀ ⦃v w⦄, G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

theorem isBipartite_iff :
  G.IsBipartite s t ↔ Disjoint s t
    ∧ ∀ ⦃v w⦄, G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s := by rfl

theorem isBipartite_comm :
    G.IsBipartite s t ↔ G.IsBipartite t s := by
  simp [isBipartite_iff, disjoint_comm, or_comm]

/-- Suppose `G` is bipartite in `s` and `t`. If `v ∈ s` is adjacent to `w`
then `w ∈ t`. -/
theorem isBipartite_adj (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.Adj v w → w ∈ t := by
  intro hadj
  apply h.2 at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.1 hv
  simpa [hv, nhv] using hadj

theorem isBipartite_neighborSet (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_setOf_eq, iff_and_self]
  exact isBipartite_adj h hv

theorem isBipartite_neighborSet_subset (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartite_neighborSet h hv]
  exact Set.sep_subset t _

/-- Suppose `G` is bipartite in `s` and `t`. If `w ∈ t` is adjacent to `v`
then `v ∈ s`. -/
theorem isBipartite_adj' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.Adj v w → v ∈ s := by
  intro hadj
  apply h.2 at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.1 hw
  simpa [hw, nhw] using hadj

theorem isBipartite_neighborSet' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_setOf_eq, iff_and_self]
  exact isBipartite_adj' h hw

theorem isBipartite_neighborSet_subset' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartite_neighborSet' h hw]
  exact Set.sep_subset s _

/-- Suppose `G` is bipartite in `s` and `t`. The vertices that form edges in
`G` are contained in `s ∪ t`. -/
lemma isBipartite_support_subset_union (h : G.IsBipartite s t) :
    G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  rw [Set.mem_union]
  have h_mem := h.2 hadj
  rw [or_and_left, and_or_right] at h_mem
  exact h_mem.1.1

variable [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

theorem isBipartite_neighborFinset (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborFinset v = t.filter (G.Adj v ·) := by
  ext w
  rw [mem_neighborFinset, Finset.mem_filter, iff_and_self]
  exact isBipartite_adj h hv

theorem isBipartite_bipartiteAbove (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborFinset v = Finset.bipartiteAbove G.Adj t v := by
  rw [isBipartite_neighborFinset h hv, Finset.bipartiteAbove]

theorem isBipartite_neighborFinset_subset
    (h : G.IsBipartite s t) (hv : v ∈ s) : G.neighborFinset v ⊆ t := by
  rw [isBipartite_neighborFinset h hv]
  exact Finset.filter_subset _ t

/-- Suppose `G` is bipartite in `s` and `t`. The degree of `v ∈ s` is at most
the cardinality of `t`. -/
theorem isBipartite_degree_le (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.degree v ≤ t.card := by
  rw [←card_neighborFinset_eq_degree]
  exact Finset.card_le_card (isBipartite_neighborFinset_subset h hv)

theorem isBipartite_neighborFinset' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborFinset w = s.filter (G.Adj · w) := by
  ext v
  rw [mem_neighborFinset, adj_comm, Finset.mem_filter, iff_and_self]
  exact isBipartite_adj' h hw

theorem isBipartite_bipartiteBelow (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborFinset w = Finset.bipartiteBelow G.Adj s w := by
  rw [isBipartite_neighborFinset' h hw, Finset.bipartiteBelow]

theorem isBipartite_neighborFinset_subset'
    (h : G.IsBipartite s t) (hw : w ∈ t) : G.neighborFinset w ⊆ s := by
  rw [isBipartite_neighborFinset' h hw]
  exact Finset.filter_subset _ s

/-- Suppose `G` is bipartite in `s` and `t`. The degree of `w ∈ t` is at most
the cardinality of `s`. -/
theorem isBipartite_degree_le' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.degree w ≤ s.card := by
  rw [←card_neighborFinset_eq_degree]
  exact Finset.card_le_card (isBipartite_neighborFinset_subset' h hw)

/-- Suppose `G` is bipartite in `s` and `t`. The sum of the degrees of vertices
in `s` is equal to the sum of the degrees of vertices in `t`.

See `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
lemma isBipartite_sum_degrees_eq (h : G.IsBipartite s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  simp_rw [←Finset.sum_attach t, ←Finset.sum_attach s,
    ←card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartite_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartite_bipartiteBelow h w.prop]
  simp_rw [Finset.sum_attach s fun w ↦ (Finset.bipartiteAbove G.Adj t w).card,
    Finset.sum_attach t fun v ↦ (Finset.bipartiteBelow G.Adj s v).card]
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

/-- The degree-sum formula refined to the vertices that form edges.

See `sum_degrees_eq_twice_card_edges`. -/
theorem sum_degrees_support_eq_twice_card_edges [DecidableEq V] :
    ∑ v ∈ G.support, G.degree v = 2 * G.edgeFinset.card := by
  rw [←card_edgeFinset_induce_support_eq]
  simp_rw [←sum_degrees_eq_twice_card_edges, ←degree_restrict_eq_induce,
    degree_restrict_support_eq,
    ←Finset.sum_toFinset_eq_subtype (· ∈ G.support) (G.degree ·),
    Set.setOf_mem_eq]

lemma isBipartite_sum_degrees_eq_twice_card_edges
    [DecidableEq V] (h : G.IsBipartite s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * G.edgeFinset.card := by
  have h_sub : G.support ⊆ ↑s ∪ ↑t := isBipartite_support_subset_union h
  rw [←Finset.coe_union, ←Set.toFinset_subset] at h_sub
  rw [←Finset.sum_subset h_sub]
  exact sum_degrees_support_eq_twice_card_edges
  intro v _ hv
  rwa [Set.mem_toFinset, ←degree_eq_zero_iff] at hv

/-- The degree-sum formula for bipartite graphs.

See `sum_degrees_eq_twice_card_edges`. -/
theorem isBipartite_sum_degrees_eq_card_edges
    [DecidableEq V] (h : G.IsBipartite s t) :
    G.edgeFinset.card = ∑ v ∈ s, G.degree v := by
  rw [←Nat.mul_left_cancel_iff zero_lt_two,
    ←isBipartite_sum_degrees_eq_twice_card_edges h,
    Finset.sum_union (Finset.disjoint_coe.mp h.1), two_mul, add_right_inj]
  exact isBipartite_sum_degrees_eq (isBipartite_comm.mp h)

/-- The degree-sum formula for bipartite graphs.

See `sum_degrees_eq_twice_card_edges`. -/
theorem isBipartite_sum_degrees_eq_card_edges'
    [DecidableEq V] (h : G.IsBipartite s t) :
    G.edgeFinset.card = ∑ v ∈ t, G.degree v :=
  isBipartite_sum_degrees_eq_card_edges (isBipartite_comm.mp h)

end IsBipartite

section Between

/-- The edges in `G` that connect a vertex in `s` to a vertex in `t`. -/
abbrev between (s t : Set V) (G : SimpleGraph V) :
  SimpleGraph V := G.restrict (s ∪ t) \ (G.restrict s ⊔ G.restrict t)

theorem between_comm : G.between s t = G.between t s := by
  rw [between, Set.union_comm, sup_comm, ←between]

theorem between_adj :
    (G.between s t).Adj v w ↔ G.Adj v w
      ∧ (v ∈ s \ t ∧ w ∈ t \ s ∨ v ∈ t \ s ∧ w ∈ s \ t) := by
  simp_rw [sdiff_adj, sup_adj, restrict_adj]
  by_cases h₁ : v ∈ s <;> by_cases h₂ : w ∈ s
    <;> by_cases h₃ : v ∈ t <;> by_cases h₄ : w ∈ t
  all_goals simp [h₁, h₂, h₃, h₄]

theorem between_le (s t : Set V) :
    G.between s t ≤ G := by
  intro v w
  rw [between_adj]
  exact And.left

theorem between_adj_of_disjoint (h : Disjoint s t) :
    (G.between s t).Adj v w ↔ G.Adj v w
      ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) := by
  rw [between_adj, Disjoint.sdiff_eq_left h,
    Disjoint.sdiff_eq_left (disjoint_comm.mp h)]

theorem _root_.Disjoint.sdiff_sdiff_comm
    {α : Type*} [GeneralizedBooleanAlgebra α] {a b : α} :
    Disjoint (a \ b) (b \ a) := by
  rw [disjoint_iff_inf_le, ←inf_sdiff_assoc, inf_sdiff_self_left, bot_sdiff]

/-- The edges in `G` that connect a vertex in `s` to a vertex in `t` form a
bipartite graph in `s \ t` and `t \ s`. -/
theorem isBipartite_between :
    (G.between s t).IsBipartite (s \ t) (t \ s) := by
  refine ⟨Disjoint.sdiff_sdiff_comm, ?_⟩
  intro _ _ hadj
  rw [between_adj] at hadj
  exact hadj.2

/-- The edges in `G` that connect a vertex in `s` to a vertex in `t` form a
bipartite graph in `s` and `t`, provided that  `s` and `t` are disjoint. -/
theorem isBipartite_between_of_disjoint (h : Disjoint s t) :
    (G.between s t).IsBipartite s t := by
  refine ⟨h, ?_⟩
  intro _ _ hadj
  rw [between_adj_of_disjoint h] at hadj
  exact hadj.2

lemma card_edgeFinset_sup [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    (G₁ ⊔ G₂).edgeFinset.card = G₁.edgeFinset.card + G₂.edgeFinset.card
      - (G₁ ⊓ G₂).edgeFinset.card := by
  rw [edgeFinset_sup, edgeFinset_inf]
  exact Finset.card_union _ _

lemma card_edgeFinset_sup_of_disjoint [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (h : Disjoint G₁ G₂) :
    (G₁ ⊔ G₂).edgeFinset.card = G₁.edgeFinset.card + G₂.edgeFinset.card := by
  rw [edgeFinset_sup]
  apply Finset.card_union_of_disjoint
  rwa [←disjoint_edgeSet, ←Set.disjoint_toFinset] at h

lemma card_edgeFinset_inf [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    (G₁ ⊓ G₂).edgeFinset.card = G₁.edgeFinset.card + G₂.edgeFinset.card
      - (G₁ ⊔ G₂).edgeFinset.card := by
  rw [edgeFinset_inf, edgeFinset_sup]
  exact Finset.card_inter _ _

lemma card_edgeFinset_inf_of_disjoint [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (h : Disjoint G₁ G₂) :
    (G₁ ⊓ G₂).edgeFinset.card = 0 := by
  rw [edgeFinset_inf, Finset.card_eq_zero, ←Set.toFinset_inter,
    Set.toFinset_eq_empty, Disjoint.inter_eq]
  rwa [←disjoint_edgeSet] at h

lemma card_edgeFinset_sdiff_of_le [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] (h : G₂ ≤ G₁) :
    G₁.edgeFinset.card = (G₁ \ G₂).edgeFinset.card + G₂.edgeFinset.card := by
  rw [←edgeFinset_subset_edgeFinset] at h
  rw [edgeFinset_sdiff, Finset.card_sdiff h, Nat.sub_add_cancel]
  exact Finset.card_le_card h

variable [Fintype V] [DecidableEq V]

/-- The edges of a simple graph in `s ∪ t` can be decomposed into the edges in
`s`, the edges in `t`, the edges between `s` and `t`, minus the edges in `s`
and `t`. -/
theorem card_edgeFinset_decomposition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Set V) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    (G.restrict (s ∪ t)).edgeFinset.card = (G.between s t).edgeFinset.card
      + ((G.restrict s).edgeFinset.card + (G.restrict t).edgeFinset.card
      - ((G.restrict s) ⊓ (G.restrict t)).edgeFinset.card) := by
  have h_le : restrict s G ⊔ restrict t G ≤ restrict (s ∪ t) G := by
    rw [sup_le_iff]
    exact ⟨restrict_le_of_subset Set.subset_union_left,
      restrict_le_of_subset Set.subset_union_right⟩
  rw [←card_edgeFinset_sup, ←card_edgeFinset_sdiff_of_le h_le]

/-- The edges of a simple graph in `s ∪ t` can be decomposed into the edges in
`s`, the edges in `t`, and the edges between `s` and `t`, provided that  `s` and
`t` are disjoint. -/
theorem card_edgeFinset_decomposition_of_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : Set V}
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (h : Disjoint s t) :
    (G.restrict (s ∪ t)).edgeFinset.card = (G.between s t).edgeFinset.card
      + (G.restrict s).edgeFinset.card + (G.restrict t).edgeFinset.card := by
  rw [card_edgeFinset_decomposition G s t,
    card_edgeFinset_inf_of_disjoint (disjoint_restrict h),
    Nat.sub_zero, add_assoc]

/-- The edges of a simple graph can be decomposed into the edges in `s`, the
edges in `sᶜ`, and the edges between `s` and `sᶜ`. -/
theorem card_edgeFinset_decomposition_of_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] :
    G.edgeFinset.card = (G.between s sᶜ).edgeFinset.card
      + (G.restrict s).edgeFinset.card
      + (G.restrict sᶜ).edgeFinset.card := by
  rw [←card_edgeFinset_decomposition_of_disjoint G disjoint_compl_right]
  simp_rw [Set.toFinset_card, Set.union_compl_self s, restrict_univ_eq]

/-- The degree of `v ∈ s` is at most the degree of `v` in the edges between `s`
and `sᶜ` and `s.card`. -/
theorem degree_le_between_degree_plus_card
    [DecidableRel G.Adj] (s : Finset V) (hv : v ∈ s) :
    G.degree v ≤ (G.between s (↑s)ᶜ).degree v + s.card := by
  have h' : (G.between s (↑s)ᶜ).IsBipartite s ↑(sᶜ) := by
    rw [Finset.coe_compl]
    exact isBipartite_between_of_disjoint disjoint_compl_right
  have h_disjoint :
      Disjoint ((G.between s (↑s)ᶜ).neighborFinset v) s :=
    Finset.disjoint_of_subset_left
      (isBipartite_neighborFinset_subset h' hv) disjoint_compl_left
  rw [←card_neighborFinset_eq_degree, ←card_neighborFinset_eq_degree,
    ←Finset.card_union_of_disjoint h_disjoint]
  apply Finset.card_le_card
  intro w hadj
  rw [mem_neighborFinset] at hadj
  rw [Finset.mem_union, mem_neighborFinset, between_adj]
  by_cases hw : w ∈ s
  . right; exact hw
  . left; simp [hadj, hv, hw]

/-- The degree of `v ∈ s` is at most the degree of `v` in the edges between `s`
and `sᶜ` and `s.card`. -/
theorem degree_le_between_degree_plus_card'
    (s : Finset V) [DecidableRel G.Adj] (hv : v ∈ sᶜ) :
    G.degree v ≤ (G.between s (↑s)ᶜ).degree v + sᶜ.card := by
  convert degree_le_between_degree_plus_card sᶜ hv using 3
  rw [Finset.coe_compl, compl_compl]
  exact between_comm

end Between
