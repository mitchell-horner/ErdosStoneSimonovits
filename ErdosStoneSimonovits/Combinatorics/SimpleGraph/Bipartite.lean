import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.DegreeSum

open BigOperators Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartiteWith

/-- `G` is bipartite in sets `s` and `t` iff `s` and `t` are disjoint and if vertices `v` and `w`
are adjacent in `G` then `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`. -/
structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
  disjoint := h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v ∈ t) (w ∈ s), @and_comm (v ∈ s) (w ∈ t)]
    exact h.mem_of_adj hadj.symm

theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then if `v` is adjacent to `w` in `G` then `w ∈ t`. -/
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t := by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is the set of vertices in
`t` adjacent to `v` in `G`. -/
theorem isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is a subset of `t`. -/
theorem isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is disjoint to `s`. -/
theorem isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then if `v` is adjacent to `w` in `G` then `v ∈ s`. -/
theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w ∈ t) (hadj : G.Adj v w) : v ∈ s := by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is the set of vertices in
`s` adjacent to `w` in `G`. -/
theorem isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is a subset of `s`. -/
theorem isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

/-- If `G.IsBipartiteWith s t`, then the support of `G` is a subset of `s ∪ t`. -/
theorem isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is disjoint to `t`. -/
theorem isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

variable [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
in `s` adjacent to `v` in `G`. -/
theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
"above" `v` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv]
  rfl

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is disjoint to `s`. -/
theorem isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the degree of `v` in `G` is at most the size of
`t`. -/
theorem isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v ∈ s) : G.degree v ≤ #t := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
in `s` adjacent to `w` in `G`. -/
theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
"below" `w` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw]
  rfl

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is disjoint to `t`. -/
theorem isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the degree of `w` in `G` is at most the size of
`s`. -/
theorem isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w ∈ t) : G.degree w ≤ #s := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

/-- If `G.IsBipartiteWith s t`, then the sum of the degrees of vertices in `s` is equal to the sum
of the degrees of vertices in `t`.
See `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
theorem isBipartiteWith_sum_degrees_eq (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w ↦ #(bipartiteAbove G.Adj t w),
    sum_attach t fun v ↦ #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [DecidableEq V]

lemma isBipartiteWith_sum_degrees_eq_twice_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support ⊆ ↑s ∪ ↑t := isBipartiteWith_support_subset h
  rw [← coe_union, ← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub, ← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_not_mem_support] at hv

/-- The degree-sum formula for bipartite graphs, summing over the "left" part.
See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right". -/
theorem isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = #G.edgeFinset := by
  rw [← Nat.mul_left_cancel_iff zero_lt_two, ← isBipartiteWith_sum_degrees_eq_twice_card_edges h,
    sum_union (disjoint_coe.mp h.disjoint), two_mul, add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

/-- The degree-sum formula for bipartite graphs, summing over the "right" part.
See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` for the version from the "left". -/
theorem isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) :
    ∑ v ∈ t, G.degree v = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h.symm

end IsBipartiteWith

section Between

/-- The simple graph of edges that connect a vertex in the set `s` to a vertex in the set `t` in
the simple graph `G`. -/
def between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)
  symm v w := by tauto

lemma between_adj :
    (G.between s t).Adj v w ↔ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) := by rfl

lemma between_comm : G.between s t = G.between t s := by
  ext v w
  simp [between_adj, or_comm]

instance [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] [DecidableRel G.Adj] :
    DecidableRel (G.between s t).Adj := by
  intro v w
  rw [between_adj]
  infer_instance

/-- `G.between s t` is bipartite if the sets `s` and `t` are disjoint. -/
theorem between_isBipartiteWith (h : Disjoint s t) :
    (G.between s t).IsBipartiteWith s t where
  disjoint := h
  mem_of_adj v w := by
    rw [between_adj]
    tauto

/-- The neighbor set of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
lemma neighborSet_subset_between_union (hv : v ∈ s) :
    G.neighborSet v ⊆ (G.between s sᶜ).neighborSet v ∪ s := by
  simp_rw [neighborSet, between_adj, Set.setOf_subset, Set.mem_union, Set.mem_setOf]
  intro w hadj
  by_cases hw : w ∈ s
  all_goals tauto

/-- The neighbor set of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to `w`
in `G`. -/
lemma neighborSet_subset_between_union' (hw : w ∈ sᶜ) :
    G.neighborSet w ⊆ (G.between s sᶜ).neighborSet w ∪ sᶜ := by
  simp_rw [neighborSet, between_adj, Set.setOf_subset, Set.mem_union, Set.mem_setOf]
  intro v hadj
  by_cases hv : v ∈ s
  all_goals tauto

variable [DecidableEq V] [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/-- The neighbor finset of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
lemma neighborFinset_subset_between_union (hv : v ∈ s) :
    G.neighborFinset v ⊆ (G.between s sᶜ).neighborFinset v ∪ s := by
  conv_rhs =>
    rhs; rw [← toFinset_coe s]
  simp_rw [neighborFinset_def, ← Set.toFinset_union, Set.toFinset_subset_toFinset]
  exact neighborSet_subset_between_union hv

/-- The degree of `v ∈ s` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `s`. -/
theorem degree_le_between_plus (hv : v ∈ s) :
    G.degree v ≤ (G.between s sᶜ).degree v + s.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    rw [coe_compl]
    exact between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

/-- The neighbor finset of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to
`w` in `G`. -/
lemma neighborFinset_subset_between_union' (hw : w ∈ sᶜ) :
    G.neighborFinset w ⊆ (G.between s sᶜ).neighborFinset w ∪ sᶜ := by
  conv_rhs =>
    rhs; rw [← toFinset_coe s]
  simp_rw [neighborFinset_def, ← Set.toFinset_compl, ← Set.toFinset_union,
    Set.toFinset_subset_toFinset]
  apply neighborSet_subset_between_union'
  rwa [← mem_coe, coe_compl] at hw

/-- The degree of `w ∈ sᶜ` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `sᶜ`. -/
theorem degree_le_between_plus' (hw : w ∈ sᶜ) :
    G.degree w ≤ (G.between s sᶜ).degree w + sᶜ.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    rw [coe_compl]
    exact between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union' hw)

end Between

end SimpleGraph
