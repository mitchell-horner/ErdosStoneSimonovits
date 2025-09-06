import Mathlib
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.DeleteEdges
import ErdosStoneSimonovits.Combinatorics.SimpleGraph.Extremal.Basic
import ErdosStoneSimonovits.Order.Monotone.Basic

open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n+1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n-1 : ℝ), ← mul_div (n-1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc, mul_comm (n-1 : ℝ),
    ← mul_div (n+1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc, mul_le_mul_left (by positivity),
    ← Nat.cast_pred (by positivity), ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_mul, Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n+1), ← card_univ]
  -- double counting `(v, e) ↦ v ∉ e`
  apply card_nsmul_le_card_nsmul' (r := fun v e ↦ v ∉ e)
  -- counting `e`
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  -- counting `v`
  · intro v hv
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using card_edgeFinset_deleteIncidenceSet_le_extremalNumber h v

lemma bbdBelow_extremalNumber_div_choose_two (H : SimpleGraph W) :
    BddBelow { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := by
  refine ⟨0, fun x ⟨n, hn, hx⟩ ↦ ?_⟩
  rw [← hx]
  positivity

lemma tendsto_extremalNumber_div_choose_two (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop
      (𝓝 (sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 })) := by
  let f := fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)
  have hf_Ici : f '' (Set.Ici 2) = Set.range (fun n ↦ f (n + 2)) := by
    refine Set.ext fun x ↦ ⟨fun ⟨n, hn, hfn⟩ ↦ ⟨n - 2, ?_⟩,
      fun ⟨n, hfn⟩ ↦ ⟨n + 2, Nat.le_add_left 2 n, hfn⟩⟩
    rwa [← Nat.sub_add_cancel hn] at hfn
  suffices h : Tendsto (fun n ↦ f (n + 2)) atTop (𝓝 (⨅ n, f (n + 2))) by
    rwa [tendsto_add_atTop_iff_nat 2, ← sInf_range, ← hf_Ici, Set.image] at h
  apply tendsto_atTop_ciInf
  · rw [antitone_add_nat_iff_antitoneOn_nat_Ici]
    exact antitoneOn_extremalNumber_div_choose_two H
  · rw [← hf_Ici, Set.image]
    exact bbdBelow_extremalNumber_div_choose_two H

/-- The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H / n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)

theorem turanDensity_eq_sInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  (tendsto_extremalNumber_div_choose_two H).limUnder_eq

theorem turanDensity_le_extremalNumber_div_choose_two (H : SimpleGraph W) {n : ℕ} (hn : n ≥ 2) :
    turanDensity H ≤ extremalNumber n H / n.choose 2 := by
  rw [turanDensity_eq_sInf H]
  exact csInf_le (bbdBelow_extremalNumber_div_choose_two H) ⟨n, hn, rfl⟩

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  rw [turanDensity_eq_sInf H]
  exact tendsto_extremalNumber_div_choose_two H

/-- `extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
theorem isEquivalent_extremalNumber (h : turanDensity H ≠ 0) :
    (fun n ↦ (extremalNumber n H : ℝ)) ~[atTop] (fun n ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1/turanDensity H : ℝ) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn ↦ ?_⟩
    simp [h, Nat.choose_eq_zero_iff, hn]
  simpa [isEquivalent_iff_tendsto_one hz] using hπ

end SimpleGraph
