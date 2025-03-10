import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.DeleteEdges
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic

open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section TuranDensity

/-- If `G` is `H.Free`, then `G.deleteIncidenceSet v` is also `H.Free` and has at most
`extremalNumber { x // x ≠ v } H` many edges. -/
theorem card_deleteIncidenceSet_le_extremalNumber_of_free
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] (h : H.Free G) (v : V) :
    #(G.deleteIncidenceSet v).edgeFinset ≤ extremalNumber { x // x ≠ v } H := by
  let e : ({v}ᶜ : Set V) ≃ { x // x ≠ v } := by
    simpa [Set.Elem, Set.mem_compl_iff, Set.not_mem_singleton_iff]
      using (Equiv.refl { x // x ≠ v })
  rw [← card_edgeFinset_induce_compl_singleton, ← extremalNumber_congr e Iso.refl]
  apply le_extremalNumber
  contrapose! h
  rw [not_free] at h ⊢
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

lemma extremalNumber_div_choose_two_succ_le {n : ℕ} (hn : 2 ≤ n) :
    (extremalNumber (Fin (n+1)) H / (n+1).choose 2 : ℝ)
      ≤ (extremalNumber (Fin n) H / n.choose 2 : ℝ) := by
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg (Fin (n+1)) H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn)]
  suffices #G.edgeFinset * (n-1) ≤ extremalNumber (Fin n) H * (n+1) by
    rw [mul_comm (n.choose 2 : ℝ) _, Nat.cast_choose_two, ← mul_div_assoc,
      mul_comm ((n+1).choose 2 : ℝ) _, Nat.cast_choose_two, ← mul_div_assoc,
      div_le_div_iff_of_pos_right zero_lt_two, ← Nat.cast_pred (by positivity),
      ← Nat.cast_pred (by positivity), mul_comm (n : ℝ) _, ← mul_assoc, ← mul_assoc,
      add_tsub_cancel_right n 1, mul_le_mul_right (by positivity)]
    assumption_mod_cast
  -- double-counting v ∉ e
  let s := (univ ×ˢ G.edgeFinset).filter fun (v, e) ↦ v ∉ e
  trans #s
  -- counting e
  · conv_rhs =>
      rw [card_filter, sum_product_right]
      enter [2, y]
      rw [← card_filter]
    simp_rw [Sym2.mem_toFinset, filter_not, filter_mem_eq_inter, ← sum_attach G.edgeFinset,
      univ_inter, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset,
      sum_const, card_attach, smul_eq_mul, Nat.succ_sub_succ_eq_sub, le_refl]
  -- counting v
  · conv_rhs =>
      rw [← Fintype.card_fin (n+1), ← card_univ, mul_comm, ← smul_eq_mul, ← sum_const]
    conv_lhs =>
      rw [card_filter, sum_product]
      enter [2, x]
      rw [← card_filter]
    apply sum_le_sum
    intro i _
    let e : { x // x ≠ i } ≃ Fin n := Fintype.equivFinOfCardEq (by simp)
    rw [← edgeFinset_deleteIncidenceSet_eq_filter, extremalNumber_congr e.symm Iso.refl]
    exact card_deleteIncidenceSet_le_extremalNumber_of_free h i

/-- The limit `extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞` exists. -/
lemma exists_tendsto_extremalNumber_div_choose_two (H : SimpleGraph V) :
    ∃ x, Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)) atTop (𝓝 x) := by
  let f := fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)
  suffices h : ∃ x, Tendsto (fun (n : ℕ) ↦ f (n + 2)) atTop (𝓝 x) by
    simpa [tendsto_add_atTop_iff_nat 2] using h
  -- limit of antitone sequence bounded from below is infimum
  use ⨅ n, f (n + 2)
  apply tendsto_atTop_ciInf
  · apply antitone_nat_of_succ_le
    intro n
    apply extremalNumber_div_choose_two_succ_le
    rw [le_add_iff_nonneg_left]
    exact Nat.zero_le n
  · simp_rw [bddBelow_def, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    use 0
    intro n
    positivity

/-- The **Turán density** of a simple graph `H` is the limit of
`extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph V) :=
  limUnder atTop fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph V) :
    Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      atTop (𝓝 (turanDensity H)) := by
  have ⟨_, h⟩ := exists_tendsto_extremalNumber_div_choose_two H
  rwa [← Tendsto.limUnder_eq h] at h

/-- `extremalNumber (Fin n) H` is asymptotically equivalent to `turanDensity H * n.choose 2` as
`n` approaches `∞`. -/
theorem isEquivalent_extremalNumber {H : SimpleGraph V} (h : turanDensity H ≠ 0) :
    (fun (n : ℕ) ↦ (extremalNumber (Fin n) H : ℝ))
      ~[atTop] (fun (n : ℕ) ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    use 2; intro n hn
    simp [h, Nat.choose_eq_zero_iff, hn]
  rw [isEquivalent_iff_tendsto_one hz]
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / (turanDensity H) : ℝ) at hπ
  simp_rw [one_div_mul_cancel h] at hπ
  convert hπ
  field_simp [Pi.div_apply]

end TuranDensity

end SimpleGraph
