import Mathlib

import ErdosStoneSimonovits.Extremal
import ErdosStoneSimonovits.SpecialGraphs
import ErdosStoneSimonovits.SpecialFunctions
import ErdosStoneSimonovits.Nat

open Fintype

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]
  (α β: Type*) [Fintype α] [Fintype β]

/-- Suppose `0 ≤ 2*e/n-s` and `n*(2*e/n-s)^s ≤ n^s*(t-1)`,
then `e ≤ (t-1)^(1/s)*n^(2-1/s)/2+s*n/2`. -/
private lemma le_of_pow_le_pow
    {e n s t : ℕ} (hn : n ≥ 1) (hs : s ≥ 1) (ht : t ≥ 1)
    (h_avg : 0 ≤ (2*e/n-s : ℝ)) (h : n*(2*e/n-s : ℝ)^s ≤ n^s*(t-1)) :
    ↑e ≤ (t-1)^(1/(s : ℝ))*n^(2-1/(s : ℝ))/2 + (s : ℝ)*(n : ℝ)/2 := by
  rwa [←Real.rpow_natCast, ←Real.rpow_natCast, mul_comm _ (t-1 : ℝ),
    ←Real.rpow_le_rpow_iff, Real.mul_rpow, Real.mul_rpow, Real.rpow_rpow_inv,
    Real.rpow_rpow_inv, mul_sub, sub_le_iff_le_add, mul_div, div_le_iff₀,
    ←mul_assoc, ←le_div_iff₀', add_mul, add_div, ←div_div,
    div_eq_mul_inv _ (n^(s : ℝ)⁻¹: ℝ), ←Real.rpow_neg_one (n^(s : ℝ)⁻¹ : ℝ),
    ←Real.rpow_mul, mul_neg_one, mul_assoc, mul_comm (n : ℝ) _,
    ←Real.rpow_add_one, mul_assoc, mul_comm (n : ℝ) _, ←Real.rpow_add_one,
    add_assoc, one_add_one_eq_two, add_comm _ 2, ←sub_eq_add_neg, ←div_div,
    div_eq_mul_inv _ (n^(s : ℝ)⁻¹ : ℝ), ←Real.rpow_neg_one (n^(s : ℝ)⁻¹ : ℝ),
    ←Real.rpow_mul, mul_neg_one, mul_assoc, mul_comm (n : ℝ) _,
    ←Real.rpow_add_one, mul_assoc, mul_comm (s : ℝ) _, ←mul_assoc,
    ←Real.rpow_add, ←add_assoc, add_neg_cancel, zero_add, Real.rpow_one,
    mul_comm _ (s : ℝ), inv_eq_one_div] at h
  all_goals first | positivity | field_simp [hn, hs, ht]

/-- A `K α,β`-free simple graph on the vertex type `V` has at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2` edges.

This is the **Kővári–Sós–Turán theorem**. -/
theorem card_edgeFinset_le_of_completeBipartiteGraph_free
    [Nonempty α] (h_card_le : card α ≤ card β)
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : (completeBipartiteGraph α β).Free G) :
    G.edgeFinset.card
      ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
        + (card α : ℝ)*(card V : ℝ)/2 := by
  haveI : Nonempty β := by
    rw [←card_pos_iff]
    exact (Nat.succ_le_of_lt card_pos).trans h_card_le
  by_cases hcardV : card V = 0
  -- if no vertices
  . have hcard_edgeFinset : G.edgeFinset.card = 0 := by
      rw [←Nat.le_zero, ←Nat.choose_zero_succ 1, ←hcardV]
      exact card_edgeFinset_le_card_choose_two
    rw [hcardV, hcard_edgeFinset, Nat.cast_zero, Real.zero_rpow,
      mul_zero, mul_zero, zero_div, add_zero]
    apply ne_of_gt
    apply sub_pos_of_lt
    exact lt_of_le_of_lt (Nat.one_div_cast_le_one (card α)) one_lt_two
  -- if vertices
  . push_neg at hcardV
    haveI : Nonempty V := by
      rwa [←Nat.pos_iff_ne_zero, card_pos_iff] at hcardV
    -- if avg degree less than `card a`
    by_cases h_avg :
        (∑ v, G.degree v : ℝ) < ((card α)*(card V) : ℝ)
    . rw [←Nat.cast_sum, sum_degrees_eq_twice_card_edges, Nat.cast_mul,
        Nat.cast_two, ←lt_div_iff' zero_lt_two] at h_avg
      trans ((card α)*(card V)/2 : ℝ)
      . exact le_of_lt h_avg
      . apply le_add_of_nonneg_left
        apply div_nonneg _ zero_le_two
        apply mul_nonneg
        . apply Real.rpow_nonneg
          field_simp [Nat.succ_le_of_lt card_pos]
        . apply Real.rpow_nonneg
          exact Nat.cast_nonneg _
    -- if avg degree at least `card α`
    . push_neg at h_avg
      rw [←le_div_iff₀ (Nat.cast_pos.mpr card_pos)] at h_avg
      have h_avg' : card α-1 ≤ (∑ v, ↑(G.degree v) : ℝ)/(card V) := by
        trans (card α : ℝ)
        . rw [←Nat.cast_pred card_pos, Nat.cast_le]
          exact Nat.pred_le (card α)
        . exact h_avg
      -- double-counting vertices and subsets
      let X := (Finset.univ ×ˢ Finset.univ.powersetCard (card α)).filter
        fun (v, s) ↦ s ⊆ G.neighborFinset v
      -- counting over vertices
      have hcardX_eq : X.card = ∑ v : V, (G.degree v).choose (card α) := by
        suffices h_eq : ∀ v : V,
            (Finset.univ.powersetCard (card α)).filter (· ⊆ G.neighborFinset v)
              = (G.neighborFinset v).powersetCard (card α) by
          simp_rw [Finset.card_filter _, Finset.sum_product,
            ←Finset.card_filter _, h_eq, Finset.card_powersetCard,
            card_neighborFinset_eq_degree]
        intro; ext
        rw [Finset.mem_filter, Finset.mem_powersetCard_univ, and_comm,
          ←Finset.mem_powersetCard]
      have hcardX_ge : (X.card : ℝ)
          ≥ ((card V)*(2*G.edgeFinset.card/(card V)
              -(card α))^(card α)/(card α).factorial : ℝ) := by
        rw [hcardX_eq, Nat.cast_sum]
        trans ((card V)*((descPochhammer ℝ (card α)).eval
            ((∑ v, G.degree v : ℝ)/(card V))/(card α).factorial) : ℝ)
        . rw [ge_iff_le, ←le_inv_mul_iff₀ (by positivity), Finset.mul_sum,
            div_eq_mul_inv _ (card V : ℝ), mul_comm _ (card V : ℝ)⁻¹,
            Finset.mul_sum]
          apply descPochhammer_eval_le_sum_choose (Nat.succ_le_of_lt card_pos)
          . intros; positivity
          . field_simp
          . rwa [div_eq_mul_inv, mul_comm, Finset.mul_sum] at h_avg'
        . rw [←Nat.cast_two, ←Nat.cast_mul, ←sum_degrees_eq_twice_card_edges,
            Nat.cast_sum,mul_div, ge_iff_le, div_le_div_right (by positivity),
            mul_le_mul_left (by positivity)]
          trans ((∑ x : V, ↑(G.degree x))/(card V)-(card α)+1)^(card α)
          . apply pow_le_pow_left
            . rwa [←sub_nonneg] at h_avg
            . rw [sub_add, sub_le_sub_iff_left, ←Nat.cast_pred card_pos,
                Nat.cast_le]
              exact Nat.pred_le (card α)
          . exact sub_pow_le_descPochhammer_eval
              (Nat.succ_le_of_lt card_pos) h_avg'
      -- counting over subsets
      have hcardX_le : X.card ≤ ((card V).choose (card α))*(card β-1) := by
        suffices h_le : ∀ s ∈ Finset.univ.powersetCard (card α),
            (Finset.univ.filter (s ⊆ G.neighborFinset ·)).card ≤ card β-1 by
          simp_rw [Finset.card_filter _, Finset.sum_product_right,
            ←Finset.card_filter _, ←(Finset.card_univ (α := V)),
            ←Finset.card_powersetCard, ←smul_eq_mul, ←Finset.sum_const]
          exact Finset.sum_le_sum h_le
        intro A hA_mem
        by_contra! h_le
        have ⟨B, hB⟩ := Finset.exists_subset_card_eq h_le
        rw [←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at hB
        have hB_powersetCard : B ∈ Finset.univ.powersetCard (card β) := by
          rw [Finset.mem_powersetCard_univ]
          exact hB.2
        absurd h
        rw [isIsoSubgraph_completeBipartiteGraph_iff]
        use ⟨A, hA_mem⟩, ⟨B, hB_powersetCard⟩
        intro v₁ hv₁ v₂ hv₂
        replace hv₂ := hB.1 hv₂
        rw [Finset.mem_filter] at hv₂
        replace hv₁ := hv₂.2 hv₁
        rw [mem_neighborFinset] at hv₁
        exact hv₁.symm
      replace hcardX_le : (X.card : ℝ)
          ≤ (((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ) := by
        trans ((card V).choose (card α))*(card β-1)
        . rw [←Nat.cast_pred card_pos, ←Nat.cast_mul, Nat.cast_le]
          exact hcardX_le
        . apply mul_le_mul_of_nonneg _ (by trivial) (by positivity) _
          . exact Nat.choose_le_pow_div (card α) (card V)
          . rw [sub_nonneg, ←Nat.cast_one, Nat.cast_le]
            exact Nat.succ_le_of_lt card_pos
      -- solve for `G.edgeFinset.card`
      apply le_of_pow_le_pow card_pos card_pos card_pos
      . rwa [←Nat.cast_sum, sum_degrees_eq_twice_card_edges, Nat.cast_mul,
          Nat.cast_two, ←sub_nonneg] at h_avg
      . have h_card_edgeFinset := hcardX_ge.trans hcardX_le
        rwa [mul_comm _ (card β-1 : ℝ), mul_div,
          div_le_div_right (by positivity),
          mul_comm (card β-1 : ℝ) _] at h_card_edgeFinset

/-- Suppose `card α ≤ card β`. The extremal numbers of the
`α,β`-complete bi-partite graphs on the type `V` are at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2`.

See `card_edgeFinset_le_of_completeBipartiteGraph_free`. -/
theorem extremalNumber_completeBipartiteGraph_le
  [Nonempty α] (h_card_le : card α ≤ card β) :
  extremalNumber V (completeBipartiteGraph α β)
    ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
      + (card α : ℝ)*(card V : ℝ)/2 := by
  haveI : Nonempty β := by
    rw [←card_pos_iff]
    exact (Nat.succ_le_of_lt card_pos).trans h_card_le
  have h_nonneg : 0 ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
      + (card α : ℝ)*(card V : ℝ)/2 := by
    rw [←add_div]
    apply div_nonneg _ zero_le_two
    apply add_nonneg
    . apply mul_nonneg
      . apply Real.rpow_nonneg
        rw [sub_nonneg, Nat.one_le_cast]
        exact Nat.succ_le_of_lt card_pos
      . exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    . exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp_rw [extremalNumber_le_iff_of_nonneg _ _ h_nonneg]
  intro G _ h_free
  exact card_edgeFinset_le_of_completeBipartiteGraph_free α β h_card_le h_free
