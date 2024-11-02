import Mathlib

import ErdosStoneSimonovits.Extremal
import ErdosStoneSimonovits.SpecialGraphs
import ErdosStoneSimonovits.SpecialFunctions
import ErdosStoneSimonovits.Nat

open Fintype

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]
  (α β: Type*) [Fintype α] [Fintype β]

/-- A `K α,β`-free simple graph on the vertex type `V` has at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2` edges.

This is the **Kővári–Sós–Turán theorem**. -/
theorem card_edgeFinset_le_of_completeBipartiteGraph_free
    [Nonempty α] (h_card_le : card α ≤ card β)
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ¬(completeBipartiteGraph α β).IsIsoSubgraph G) :
    G.edgeFinset.card
      ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
        + (card α : ℝ)*(card V : ℝ)/2 := by
  haveI : Nonempty β := by
    rw [←card_pos_iff]
    exact (Nat.succ_le_of_lt card_pos).trans h_card_le
  by_cases hcardV : card V = 0
  -- if no vertices
  . have hcard_edgeFinset : G.edgeFinset.card = 0 := by
      rw [←Nat.le_zero]
      convert card_edgeFinset_le_card_choose_two
      rw [hcardV, Nat.choose_zero_succ]
    rw [hcardV, hcard_edgeFinset, Nat.cast_zero, Real.zero_rpow]
    . field_simp
    . apply ne_of_gt
      apply sub_pos_of_lt
      exact lt_of_le_of_lt (Nat.one_div_cast_le_one _) one_lt_two
  -- if vertices
  . push_neg at hcardV
    haveI : Nonempty V := by
      rw [←card_pos_iff]
      rwa [←Nat.pos_iff_ne_zero] at hcardV
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
      have h_avg' : (card α-1 : ℝ) ≤ ((∑ v, ↑(G.degree v))/(card V) : ℝ) := by
        apply h_avg.trans'
        rw [←Nat.cast_pred card_pos, Nat.cast_le]
        exact Nat.pred_le _
      -- double-counting vertices and subsets
      let X := (Finset.univ ×ˢ Finset.univ.powersetCard (card α)).filter
        fun (v, s) ↦ s ⊆ G.neighborFinset v
      -- counting over vertices
      have h_eq : X.card = ∑ v : V, (G.degree v).choose (card α) := by
        suffices h_eq : ∀ v : V,
            (Finset.univ.powersetCard (card α)).filter (· ⊆ G.neighborFinset v)
              = (G.neighborFinset v).powersetCard (card α) by
          simp_rw [Finset.card_filter _, Finset.sum_product,
            ←Finset.card_filter _, h_eq, Finset.card_powersetCard,
            card_neighborFinset_eq_degree]
        intro v; ext S
        rw [Finset.mem_filter, Finset.mem_powersetCard_univ,
          and_comm, ←Finset.mem_powersetCard]
      have h_ge : (X.card : ℝ)
          ≥ ((card V)*(2*G.edgeFinset.card/(card V)
              -(card α))^(card α)/(card α).factorial : ℝ) := by
        rw [h_eq, Nat.cast_sum]
        trans ((card V)*((descPochhammer ℝ (card α)).eval
            ((∑ v, G.degree v : ℝ)/(card V))/(card α).factorial) : ℝ)
        . rw [ge_iff_le, ←le_inv_mul_iff₀ (Nat.cast_pos.mpr card_pos),
            Finset.mul_sum, div_eq_mul_inv _ (card V : ℝ),
            mul_comm _ (card V : ℝ)⁻¹, Finset.mul_sum]
          apply descPochhammer_eval_le_sum_choose (Nat.succ_le_of_lt card_pos)
          . intro i _
            exact inv_nonneg_of_nonneg (Nat.cast_nonneg _)
          . field_simp
          . rw [←Finset.mul_sum, mul_comm (card V : ℝ)⁻¹ _, ←div_eq_mul_inv]
            exact h_avg'
        . rw [mul_div, ge_iff_le,
            div_le_div_right (Nat.cast_pos.mpr (Nat.factorial_pos _)),
            mul_le_mul_left (Nat.cast_pos.mpr card_pos),
            ←Nat.cast_two, ←Nat.cast_mul,
            ←sum_degrees_eq_twice_card_edges, Nat.cast_sum]
          trans ((∑ x : V, ↑(G.degree x))/(card V)-(card α)+1)^(card α)
          . apply pow_le_pow_left
            . rw [sub_nonneg]
              exact h_avg
            . rw [sub_add, sub_le_sub_iff_left,
                ←Nat.cast_pred card_pos, Nat.cast_le]
              exact Nat.pred_le _
          . exact sub_pow_le_descPochhammer_eval
              (Nat.succ_le_of_lt card_pos) h_avg'
      -- counting over subsets
      have h_le : X.card ≤ ((card V).choose (card α))*(card β-1) := by
        suffices h_le : ∀ s ∈ Finset.univ.powersetCard (card α),
            (Finset.univ.filter (s ⊆ G.neighborFinset ·)).card ≤ card β-1 by
          simp_rw [Finset.card_filter _, Finset.sum_product_right,
            ←Finset.card_filter _, ]
          trans ∑ s ∈ (Finset.univ : Finset V).powersetCard (card α), (card β-1)
          . exact Finset.sum_le_sum h_le
          . rw [Finset.sum_const, Finset.card_powersetCard,
              Finset.card_univ, smul_eq_mul]
        intro A hA_powersetCard
        by_contra! h_le
        have ⟨B, hB⟩ := Finset.exists_subset_card_eq h_le
        rw [←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at hB
        have hB_powersetCard : B ∈ Finset.univ.powersetCard (card β) := by
          rw [Finset.mem_powersetCard_univ]
          exact hB.2
        absurd h
        rw [isIsoSubgraph_completeBipartiteGraph_iff]
        use ⟨A, hA_powersetCard⟩, ⟨B, hB_powersetCard⟩
        intro v₁ hv₁ v₂ hv₂
        replace hv₂ := hB.1 hv₂
        rw [Finset.mem_filter] at hv₂
        replace hv₁ := hv₂.2 hv₁
        rw [mem_neighborFinset] at hv₁
        exact hv₁.symm
      replace h_le : (X.card : ℝ)
          ≤ (((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ) := by
        rw [←Nat.cast_pow]
        trans (↑((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ)
        . rw [←Nat.cast_pred card_pos, ←Nat.cast_mul, Nat.cast_le]
          trans ((card V).choose (card α))*(card β-1)
          . exact h_le
          . apply Nat.mul_le_mul_right
            trans ((card V).descFactorial (card α))/((card α).factorial)
            . rw [Nat.choose_eq_descFactorial_div_factorial]
            . apply Nat.div_le_div_right
              exact Nat.descFactorial_le_pow (card V) (card α)
        . apply mul_le_mul_of_nonneg _ (le_refl _) (Nat.cast_nonneg _) _
          . exact Nat.cast_div_le
          . rw [sub_nonneg, ←Nat.cast_one, Nat.cast_le]
            exact Nat.succ_le_of_lt card_pos
      have h_card_edgeFinset := h_ge.trans h_le
      -- inequalities involving `card α`, `card β`
      have hcardα_pos : 0 < (card α : ℝ) := by
        rw [Nat.cast_pos]
        exact card_pos
      have hcardα_inv_pos : 0 < (card α : ℝ)⁻¹ := by
        rw [inv_pos]
        exact hcardα_pos
      have hcardα_factorial_pos : 0 < ((card α).factorial : ℝ) := by
        rw [Nat.cast_pos]
        exact Nat.factorial_pos _
      have hcardV_pos : 0 < (card V : ℝ) := by
        rw [Nat.cast_pos]
        exact card_pos
      have hcardβ_sub_one_nonneg : (card β-1 : ℝ) ≥ 0 := by
        field_simp [Nat.succ_le_of_lt card_pos]
      have hcardV_pow_nonneg : 0 ≤ (card V : ℝ)^(card α : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h_avg_sub_nonneg :
          0 ≤ (2*G.edgeFinset.card/(card V)-(card α) : ℝ) := by
        rw [←Nat.cast_two, ←Nat.cast_mul,
            ←sum_degrees_eq_twice_card_edges, Nat.cast_sum]
        exact sub_nonneg_of_le h_avg
      have h_avg_sub_pow_noneng :=
        Real.rpow_nonneg h_avg_sub_nonneg (card α : ℝ)
      have h_mul_avg_pow_nonneg :=
        mul_nonneg (Nat.cast_nonneg (card V)) h_avg_sub_pow_noneng
      have hcardV_pow_mul_pos : 0 < ((card V)^(card α : ℝ)⁻¹*2 : ℝ) :=
        mul_pos (Real.rpow_pos_of_pos hcardV_pos _) zero_lt_two
      have hcardβ_sub_one_cardV_pow_nonneg :=
        mul_nonneg hcardβ_sub_one_nonneg hcardV_pow_nonneg
      -- solve for `G.edgeFinset.card`
      rwa [←Real.rpow_natCast, ←Real.rpow_natCast, mul_comm _ (card β-1 : ℝ),
        mul_div, div_le_div_right hcardα_factorial_pos,
        ←Real.rpow_le_rpow_iff h_mul_avg_pow_nonneg
          hcardβ_sub_one_cardV_pow_nonneg hcardα_inv_pos,
        Real.mul_rpow (Nat.cast_nonneg _) h_avg_sub_pow_noneng,
        Real.mul_rpow hcardβ_sub_one_nonneg hcardV_pow_nonneg,
        Real.rpow_rpow_inv h_avg_sub_nonneg hcardα_pos.ne',
        Real.rpow_rpow_inv (Nat.cast_nonneg _) hcardα_pos.ne',
        mul_sub, sub_le_iff_le_add, mul_div, div_le_iff₀ hcardV_pos,
        ←mul_assoc, ←le_div_iff₀' hcardV_pow_mul_pos, add_mul, add_div,
        ←div_div, div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹: ℝ),
        ←Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ),
        ←Real.rpow_mul (Nat.cast_nonneg _), mul_neg_one, mul_assoc,
        mul_comm (card V : ℝ) _, ←Real.rpow_add_one hcardV_pos.ne', mul_assoc,
        mul_comm (card V : ℝ) _, ←Real.rpow_add_one hcardV_pos.ne', add_assoc,
        one_add_one_eq_two, add_comm _ 2, ←sub_eq_add_neg, ←div_div,
        div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹ : ℝ),
        ←Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ),
        ←Real.rpow_mul (Nat.cast_nonneg _), mul_neg_one, mul_assoc,
        mul_comm (card V : ℝ) _, ←Real.rpow_add_one hcardV_pos.ne', mul_assoc,
        mul_comm (card α : ℝ) _, ←mul_assoc, ←Real.rpow_add hcardV_pos,
        ←add_assoc, add_neg_cancel, zero_add, Real.rpow_one,
        mul_comm _ (card α : ℝ), inv_eq_one_div] at h_card_edgeFinset

/-- Suppose `s = card α ≤ card β = t`. The extremal numbers of the
`α,β`-complete bi-partite graphs on the type `V` are at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2`.

See `card_edgeFinset_le_of_completeBipartiteGraph_free`. -/
theorem extremalNumber_completeBipartiteGraph_le
  [h_nonempty : Nonempty α] (h_card_le : card α ≤ card β) :
  extremalNumber V (completeBipartiteGraph α β)
    ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
      + (card α : ℝ)*(card V : ℝ)/2 := by
  haveI h_nonempty' : Nonempty β := by
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
  intro G nh_isosub
  classical
    exact card_edgeFinset_le_of_completeBipartiteGraph_free
      α β h_card_le nh_isosub
