import Mathlib

import ErdosStoneSimonovits.Restrict
import ErdosStoneSimonovits.Extremal

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

section TuranDensity

open Topology Asymptotics

/-- The *Turán density* of a simple graph `H` is the limit of the maximum
density of `H`-free simple graphs.

See `tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph V) :=
  limUnder Filter.atTop
    fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)

theorem _root_.Sym2.coe_out_eq (e : Sym2 V) :
    (e : Set V) = {e.out.1, e.out.2} := by
  ext; simp [←Sym2.mem_iff]

noncomputable instance [DecidableEq V] (e : Sym2 V) :
    Fintype (e : Set V) := by
  rw [Sym2.coe_out_eq]
  infer_instance

lemma _root_.Sym2.card_coe_of_isDiag
    [DecidableEq V] (e : Sym2 V) (h : e.IsDiag) :
    Fintype.card (e : Set V) = 1 := by
  rw [show e = s(e.out.1, e.out.2) by simp, Sym2.mk_isDiag_iff] at h
  have h_coe_eq : (e : Set V) = {e.out.1} := by
    rw [Sym2.coe_out_eq, h, Set.insert_eq_of_mem (Set.mem_singleton _)]
  have h_cardEq : Fintype.card (e : Set V)
      = Fintype.card ({e.out.1} : Set V) := by
    rw [Fintype.card_eq, ←h_coe_eq]
    exact ⟨Equiv.refl e⟩
  rw [h_cardEq, Fintype.card_ofSubsingleton]

lemma _root_.Sym2.card_coe_of_not_isDiag
    [DecidableEq V] (e : Sym2 V) (h : ¬e.IsDiag) :
    Fintype.card (e : Set V) = 2 := by
  rw [show e = s(e.out.1, e.out.2) by simp, Sym2.mk_isDiag_iff] at h
  have h_not_mem_singleton : e.out.1 ∉ ({e.out.2} : Set V) := by
    rw [Set.not_mem_singleton_iff]
    exact h
  have h_cardEq : Fintype.card (e : Set V)
      = Fintype.card ({e.out.1, e.out.2} : Set V) := by
    rw [Fintype.card_eq, ←Sym2.coe_out_eq]
    exact ⟨Equiv.refl e⟩
  rw [h_cardEq, Set.card_insert _ h_not_mem_singleton,
    Fintype.card_ofSubsingleton]

/-- The coercion of an edge to a set contains two vertices. -/
theorem card_mem_edgeSet [DecidableEq V] (e : G.edgeSet) :
    Fintype.card (e : Set V) = 2 := by
  convert Sym2.card_coe_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet e.prop)

/-- The coercion of an edge to a set contains two vertices. -/
theorem card_mem_edgeFinset
    [DecidableEq V] [Fintype G.edgeSet] (e : G.edgeFinset) :
    Fintype.card (e : Set V) = 2 := by
  let e' : G.edgeSet := ⟨e, mem_edgeFinset.mp e.prop⟩
  rw [show e.val = e'.val by rfl]
  exact card_mem_edgeSet e'

/-- The limit in the *Turán density* of a simple graph `H` exists. -/
lemma exists_tendsto_extremalNumber_div_choose_two (H : SimpleGraph V) :
    ∃ x, Filter.Tendsto
      (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      Filter.atTop (𝓝 x) := by
  let f := fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)
  -- shift the index to avoid division by zero
  suffices h : ∃ x, Filter.Tendsto
      (fun (n : ℕ) ↦ f (n + 2)) Filter.atTop (𝓝 x) by
    conv_rhs at h =>
      intro x
      rw [Filter.tendsto_add_atTop_iff_nat 2]
    exact h
  -- the limit of an antitone sequence bounded from below is the infimum
  use ⨅ n, f (n + 2)
  apply tendsto_atTop_ciInf
  . apply antitone_nat_of_succ_le
    intro n
    apply succ_le (n+2)
    field_simp
  . simp_rw [bddBelow_def, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    use 0
    intro n
    exact extremalNumber_div_choose_two_nonneg (n + 2)
where
  extremalNumber_div_choose_two_nonneg (n : ℕ) :
      0 ≤ (extremalNumber (Fin n) H / n.choose 2 : ℝ) := by
    apply div_nonneg <;> exact Nat.cast_nonneg _
  succ_le (n : ℕ) (hn : n ≥ 2) :
      (extremalNumber (Fin (n+1)) H / (n+1).choose 2 : ℝ)
        ≤ (extremalNumber (Fin n) H / n.choose 2 : ℝ) := by
    have h_choose_two_pos : 0 < (n.choose 2 : ℝ) := by
      rw [Nat.cast_pos]
      exact Nat.choose_pos hn
    have h_succ_choose_two_pos : 0 < ((n+1).choose 2 : ℝ) := by
      rw [Nat.cast_pos]
      apply Nat.choose_pos
      apply le_of_lt
      exact lt_of_le_of_lt hn (Nat.lt_succ_self n)
    have h_nonneg :
        0 ≤ (extremalNumber (Fin n) H / n.choose 2 * (n+1).choose 2 : ℝ) :=
      mul_nonneg (extremalNumber_div_choose_two_nonneg n) (Nat.cast_nonneg _)
    rw [div_le_iff₀ h_succ_choose_two_pos,
      extremalNumber_le_iff_of_nonneg _ _ h_nonneg]
    intro G _ h
    rw [mul_comm, ←mul_div_assoc, le_div_iff₀' h_choose_two_pos]
    -- double-counting edges and vertices
    let s := (G.edgeFinset ×ˢ Finset.univ).filter fun (e, v) ↦ v ∉ e
    -- counting over edges
    have hs₁ : s.card = G.edgeFinset.card * (n-1) := by
      classical simp_rw [Finset.card_filter _ _, Finset.sum_product,
        ←Finset.card_filter, ←SetLike.mem_coe, ←Set.mem_toFinset,
        Finset.filter_not, Finset.filter_mem_eq_inter]
      conv_lhs =>
        rw [←Finset.sum_attach]
        rhs; intro e
        rw [Finset.univ_inter, ←Finset.compl_eq_univ_sdiff, Finset.card_compl,
          Fintype.card_fin, Set.toFinset_card, card_mem_edgeFinset e]
      rw [Finset.sum_const, Finset.card_attach, smul_eq_mul,
        Nat.succ_sub_succ_eq_sub]
    -- counting over vertices
    have hs₂ : s.card ≤ extremalNumber (Fin n) H * (n+1) := by
      simp_rw [Finset.card_filter _ _, Finset.sum_product_right,
        ←Finset.card_filter, ←edgeFinset_deleteIncidenceSet, Set.toFinset_card,
        deleteIncidenceSet_eq_restrict_compl_singleton G, ←Set.toFinset_card,
        card_edgeFinset_restrict_eq_induce]
      calc ∑ x, (G.induce {x}ᶜ).edgeFinset.card
        _ ≤ ∑ _, extremalNumber (Fin n) H := by
            apply Finset.sum_le_sum
            intro x _
            have h_cardEq : Fintype.card (↑{x}ᶜ : Set (Fin (n+1))) = n := by
              rw [←Set.toFinset_card, Set.toFinset_compl,
                Set.toFinset_singleton, Finset.card_compl,
                Finset.card_singleton, Fintype.card_fin]
              exact Nat.pred_succ _
            rw [←extremalNumber_eq_of_iso
              Iso.refl (Fintype.equivFinOfCardEq h_cardEq)]
            -- `n`-vertex induced subgraphs of `G` are `H`-free
            apply le_extremalNumber
            contrapose! h
            rw [not_not] at h ⊢
            exact h.trans ⟨SubgraphIso.induce G _⟩
        _ = extremalNumber (Fin n) H * (n+1) := by
            rw [Finset.sum_const, smul_eq_mul, Finset.card_univ,
              Fintype.card_fin, mul_comm]
    have h_pos : 0 < n := lt_of_lt_of_le zero_lt_two hn
    have h_cast_pos : 0 < (n : ℝ) := by
      rw [Nat.cast_pos]
      exact h_pos
    have h_succ_pos : 0 < n+1 := h_pos.trans (Nat.lt_succ_self n)
    rw [mul_comm (n.choose 2 : ℝ), Nat.cast_choose_two, ←mul_div_assoc,
      mul_comm ((n+1).choose 2 : ℝ) _, Nat.cast_choose_two, ←mul_div_assoc,
      div_le_div_right zero_lt_two, ←Nat.cast_pred h_pos,
      ←Nat.cast_pred h_succ_pos, mul_comm (n : ℝ) _, ←mul_assoc, ←mul_assoc,
      show n+1-1=n from Nat.pred_succ n, mul_le_mul_right h_cast_pos,
      ←Nat.cast_mul, ←Nat.cast_mul, Nat.cast_le]
    rw [←hs₁]
    exact hs₂

/-- The limit in the Turán density of a simple graph `H` exists. The Turán
density of `H` is well-defined from the uniqueness of limits in `ℝ`. -/
theorem tendsto_turanDensity (H : SimpleGraph V) :
    Filter.Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      Filter.atTop (𝓝 (turanDensity H)) := by
  have ⟨x, h⟩ := exists_tendsto_extremalNumber_div_choose_two H
  rwa [←Filter.Tendsto.limUnder_eq h] at h

/-- The extremal numbers of the type `Fin n` and a simple graph `H` are
asymptotically equivalent to the product of the Turán density of `H` and
`n.choose 2`. -/
theorem isEquivalent_extremalNumber
    (H : SimpleGraph V) (h : turanDensity H ≠ 0) :
    (fun (n : ℕ) ↦ (extremalNumber (Fin n) H : ℝ)) ~[Filter.atTop]
      (fun (n : ℕ) ↦ ((turanDensity H)*(n.choose 2) : ℝ)) := by
  have h_ne_zero : ∀ᶠ (x : ℕ) in Filter.atTop,
      H.turanDensity * ↑(x.choose 2) ≠ 0 := by
    rw [Filter.eventually_atTop]
    use 2
    intro n hn
    field_simp [h, Nat.choose_eq_zero_iff, hn]
  rw [isEquivalent_iff_tendsto_one h_ne_zero]
  have hπ := tendsto_turanDensity H
  apply Filter.Tendsto.const_mul (1 / (turanDensity H) : ℝ) at hπ
  simp_rw [one_div_mul_cancel h] at hπ
  convert hπ
  rw [Pi.div_apply, div_mul_div_comm, one_mul]

end TuranDensity
