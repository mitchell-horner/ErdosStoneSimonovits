import Mathlib
import ErdosStoneSimonovits.Analysis.SpecialFunctions.Pochhammer
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Finset Fintype

namespace SimpleGraph

variable {V α β : Type*} [Fintype V] [Fintype α] [Fintype β]

/-- A simple graph contains a copy of a `completeBipartiteGraph α β` iff there exists a set of
`card α` vertices adjacent to a set of `card β` vertices. -/
theorem completeBipartiteGraph_isContained_iff {G : SimpleGraph V} :
    completeBipartiteGraph α β ⊑ G
      ↔ ∃ (A : univ.powersetCard (Fintype.card α)) (B : univ.powersetCard (Fintype.card β)),
          ∀ v₁ ∈ A.val, ∀ v₂ ∈ B.val, G.Adj v₁ v₂ := by
  constructor
  · intro ⟨f⟩
    let A := univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩
    have hA : A ∈ univ.powersetCard (Fintype.card α) := by
      rw [mem_powersetCard_univ, card_map, card_univ]
    let B := univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩
    have hB : B ∈ univ.powersetCard (Fintype.card β) := by
      rw [mem_powersetCard_univ, card_map, card_univ]
    use ⟨A, hA⟩, ⟨B, hB⟩
    intro v₁ hv₁ v₂ hv₂
    rw [mem_map] at hv₁ hv₂
    obtain ⟨a, _, ha⟩ := hv₁
    obtain ⟨b, _, hb⟩ := hv₂
    rw [← ha, ← hb]
    exact f.toHom.map_adj (by simp)
  · intro ⟨⟨A, hA⟩, ⟨B, hB⟩, h⟩
    rw [mem_powersetCard_univ] at hA hB
    haveI : Nonempty (α ↪ A) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa [← card_coe] using hA.ge
    let fa : α ↪ A := Classical.arbitrary (α ↪ A)
    haveI : Nonempty (β ↪ B) := by
      apply Function.Embedding.nonempty_of_card_le
      simpa [← card_coe] using hB.ge
    let fb : β ↪ B := Classical.arbitrary (β ↪ B)
    let f : α ⊕ β ↪ V := by
      use Sum.elim (Subtype.val ∘ fa) (Subtype.val ∘ fb)
      intro ab₁ ab₂
      match ab₁, ab₂ with
      | Sum.inl a₁, Sum.inl a₂ => simp [← Subtype.ext_iff_val]
      | Sum.inr b₁, Sum.inl a₂ =>
        simpa using (h (fa a₂) (fa a₂).prop (fb b₁) (fb b₁).prop).ne'
      | Sum.inl a₁, Sum.inr b₂ =>
        simpa using (h (fa a₁) (fa a₁).prop (fb b₂) (fb b₂).prop).symm.ne'
      | Sum.inr b₁, Sum.inr b₂ => simp [← Subtype.ext_iff_val]
    use ⟨f.toFun, ?_⟩, f.injective
    intro ab₁ ab₂ hadj
    rcases hadj with ⟨hab₁, hab₂⟩ | ⟨hab₁, hab₂⟩
    all_goals dsimp [f]
    · rw [← Sum.inl_getLeft ab₁ hab₁, ← Sum.inr_getRight ab₂ hab₂,
        Sum.elim_inl, Sum.elim_inr]
      exact h (fa _) (by simp) (fb _) (by simp)
    · rw [← Sum.inr_getRight ab₁ hab₁, ← Sum.inl_getLeft ab₂ hab₂,
        Sum.elim_inl, Sum.elim_inr, adj_comm]
      exact h (fa _) (by simp) (fb _) (by simp)

variable [DecidableEq V]

section KovariSosTuran

/-- `aux` is the set of pairs `(t, v)` s.t. `t : Finset V` is an `n`-sized subset of the neighbor
finset of `v : V`.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private abbrev aux (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :=
  (univ.powersetCard n ×ˢ univ).filter fun (t, v) ↦ t ⊆ G.neighborFinset v

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If `G` is `(completeBipartiteGraph α β).Free`, then `#(aux G (card α))` is at most the number
of ways to choose `card α` vertices from `card V` vertices `card β-1` times.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma card_aux_le [Nonempty β] (h : (completeBipartiteGraph α β).Free G) :
    #(aux G (card α)) ≤ (((card V).choose (card α))*(card β-1) : ℝ) := by
  simp_rw [card_filter _, sum_product, ← card_filter, ← @card_univ V, ← card_powersetCard,
    ← nsmul_eq_mul, ← sum_const, ← Nat.cast_pred card_pos, ← Nat.cast_sum, Nat.cast_le]
  apply sum_le_sum; intro t ht_mem
  contrapose! h
  rw [not_not, completeBipartiteGraph_isContained_iff]
  have ⟨t', ht'⟩ := exists_subset_card_eq h
  rw [← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at ht'
  have ht'_mem : t' ∈ univ.powersetCard (Fintype.card β) := by
    simpa [mem_powersetCard_univ] using ht'.2
  use ⟨t, ht_mem⟩, ⟨t', ht'_mem⟩
  intro v₁ hv₁ v₂ hv₂
  replace hv₂ := ht'.1 hv₂
  rw [mem_filter] at hv₂
  replace hv₁ := hv₂.2 hv₁
  rw [mem_neighborFinset] at hv₁
  exact hv₁.symm

/-- If the average degree of vertices in `G` is at least `card α-1`, then it follows from
a special case of Jensen's inequality for `Nat.choose` that `#(aux G (card α))` is at least
`card α` times the desending pochhammer function evaluated at the average divided by
`(card α).factorial`.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma le_card_aux [Nonempty V] [Nonempty α]
    (h_avg : card α-1 ≤ (∑ v : V, G.degree v : ℝ) / card V) :
    ((card V)*((descPochhammer ℝ (card α)).eval
        ((∑ v, G.degree v : ℝ)/card V)/(card α).factorial) : ℝ) ≤ #(aux G (card α)) := by
  simp_rw [card_filter _, sum_product_right, ← card_filter, powersetCard_eq_filter,
    filter_comm, powerset_univ, filter_subset_univ, ← powersetCard_eq_filter,
    card_powersetCard, card_neighborFinset_eq_degree, Nat.cast_sum]
  rw [← le_inv_mul_iff₀ (by positivity), mul_sum,
      div_eq_mul_inv _ (card V : ℝ), mul_comm _ (card V : ℝ)⁻¹, mul_sum]
  apply descPochhammer_eval_div_factorial_le_sum_choose (by positivity) _ _ (by simp) (by simp)
  rwa [div_eq_inv_mul, mul_sum] at h_avg

/-- If the average degree of vertices in `G` is at least `card α-1` and `G` is
`(completeBipartiteGraph α β).Free`, then `G` has at most
`(card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2 + (card α-1)*(card V)/2` edges.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma card_edgeFinset_le_of_aux [Nonempty V] [Nonempty α] [Nonempty β]
    (h_avg : card α-1 ≤ (∑ v : V, G.degree v : ℝ) / card V)
    (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset
      ≤ ((card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2 + (card α-1)*(card V)/2 : ℝ) := by
  have h_one_le_card : 1 ≤ card β := card_pos
  have h_avg_sub_nonneg : 0 ≤ (2*#G.edgeFinset/card V-card α+1 : ℝ) := by
    rwa [← Nat.cast_sum, sum_degrees_eq_twice_card_edges,
      Nat.cast_mul, Nat.cast_two, ← sub_nonneg, ← sub_add] at h_avg
  suffices h : ((card V)*(2*#G.edgeFinset/card V-card α+1)^(card α)/(card α).factorial : ℝ)
      ≤ (((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ) by
    rwa [mul_comm _ (card β-1 : ℝ), mul_div, div_le_div_iff_of_pos_right,
      mul_comm (card β-1 : ℝ) _, ← Real.rpow_natCast, ← Real.rpow_natCast,
      mul_comm _ ((card β)-1 : ℝ), ← Real.rpow_le_rpow_iff, Real.mul_rpow, Real.mul_rpow,
      Real.rpow_rpow_inv, Real.rpow_rpow_inv, sub_add, mul_sub, sub_le_iff_le_add, mul_div,
      div_le_iff₀, ← mul_assoc, ← le_div_iff₀', add_mul, add_div, ← div_div,
      div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹: ℝ),
      ← Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ), ← Real.rpow_mul, mul_neg_one, mul_assoc,
      mul_comm (card V : ℝ) _, ← Real.rpow_add_one, mul_assoc, mul_comm (card V : ℝ) _,
      ← Real.rpow_add_one, add_assoc, one_add_one_eq_two, add_comm _ 2, ← sub_eq_add_neg,
      ← div_div, div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹ : ℝ),
      ← Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ), ← Real.rpow_mul, mul_neg_one, mul_assoc,
      mul_comm (card V : ℝ) _, ← Real.rpow_add_one, mul_assoc, mul_comm (card α-1 : ℝ) _,
      ← mul_assoc, ← Real.rpow_add, ← add_assoc, add_neg_cancel, zero_add, Real.rpow_one,
      mul_comm _ (card α-1 : ℝ), inv_eq_one_div] at h
    any_goals
      first | positivity | field_simp [h_one_le_card, h_avg_sub_nonneg]
  -- double-counting t ⊆ G.neighborSet v
  trans (#(aux G (card α)) : ℝ)
  -- counting t
  · trans (card V)*((descPochhammer ℝ (card α)).eval
        ((∑ v, G.degree v : ℝ)/card V)/(card α).factorial)
    · rw [← Nat.cast_two, ← Nat.cast_mul, ← sum_degrees_eq_twice_card_edges, Nat.cast_sum,
        mul_div, div_le_div_iff_of_pos_right (by positivity), mul_le_mul_left (by positivity)]
      exact pow_le_descPochhammer_eval h_avg
    · exact le_card_aux h_avg
  -- counting v
  · trans ((card V).choose (card α))*(card β-1)
    · exact card_aux_le h_free
    · apply mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (card α) (card V))
      exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)

/-- The `(completeBipartiteGraph α β).Free` simple graphs on the vertex type `V` have at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α-1)*(card V)/2` edges.

This is the **Kővári–Sós–Turán theorem**. -/
theorem card_edgeFinset_le_of_completeBipartiteGraph_free
    [Nonempty α] (hcard_le : card α ≤ card β) {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset
      ≤ ((card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2 + (card α-1)*(card V)/2 : ℝ) := by
  -- have hcardβ := card_pos.trans_le hcard_le
  haveI : Nonempty β := by
    rw [← card_pos_iff]
    exact card_pos.trans_le hcard_le
  cases isEmpty_or_nonempty V
  -- if no vertices
  · have h_two_sub_one_div_ne_zero : 2 - (card α : ℝ)⁻¹ ≠ 0 := by
      apply sub_ne_zero_of_ne ∘ ne_of_gt
      exact (card α).cast_inv_le_one.trans_lt one_lt_two
    simp [h_two_sub_one_div_ne_zero]
  -- if vertices
  · rcases lt_or_le (∑ v, G.degree v : ℝ) ((card α-1)*(card V) : ℝ) with h_sum_lt | h_avg
    -- if avg degree less than `card a-1`
    · rw [← Nat.cast_sum, sum_degrees_eq_twice_card_edges,
        Nat.cast_mul, Nat.cast_two, ← lt_div_iff₀' zero_lt_two] at h_sum_lt
      apply h_sum_lt.le.trans
      apply le_add_of_nonneg_left
      apply div_nonneg _ zero_le_two
      apply mul_nonneg
      · apply Real.rpow_nonneg _ (1/card α)
        exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)
      · exact Real.rpow_nonneg (card V).cast_nonneg (2-1/card α)
    -- -- if avg degree at least `card α-1`
    · rw [← le_div_iff₀ (mod_cast card_pos)] at h_avg
      exact card_edgeFinset_le_of_aux h_avg h_free

end KovariSosTuran

/-- The extremal numbers of `completeBipartiteGraph α β` on the type `V` are at most
`(card β-1)^(1/card α)*(card V)^(2-1/card α)/2+(card α-1)*(card V)/2`.

This is the corollary of the **Kővári–Sós–Turán theorem** for extremal numbers. -/
theorem extremalNumber_completeBipartiteGraph_le [Nonempty α] (hcard_le : card α ≤ card β) :
  extremalNumber (card V) (completeBipartiteGraph α β)
    ≤ ((card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2 + (card α-1)*(card V)/2 : ℝ) := by
  haveI : Nonempty β := by
    rw [← card_pos_iff]
    exact card_pos.trans_le hcard_le
  have h_nonneg : 0 ≤ ((card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2
      + (card α-1)*(card V)/2 : ℝ) := by
    apply add_nonneg
    · apply div_nonneg _ zero_le_two
      apply mul_nonneg _ (by positivity)
      apply Real.rpow_nonneg
      exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)
    · apply div_nonneg _ zero_le_two
      apply mul_nonneg _ (by positivity)
      exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)
  rw [extremalNumber_le_iff_of_nonneg (completeBipartiteGraph α β) h_nonneg]
  intro G _ h_free
  exact card_edgeFinset_le_of_completeBipartiteGraph_free hcard_le h_free

end SimpleGraph
