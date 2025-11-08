import Mathlib
import ErdosStoneSimonovits.Order.Monotone.Basic
import ErdosStoneSimonovits.Data.Set.Image

open Filter Metric Set TopologicalSpace Topology

namespace Real

section Monotone

/-- A monotone, bounded above sequence `f : ℕ → ℝ` has the finite limit `iSup f`. -/
theorem _root_.Real.tendsto_ciSup_of_bddAbove_monotone {f : ℕ → ℝ}
    (h_bdd : BddAbove (Set.range f)) (h_mon : Monotone f) :
    Tendsto f atTop (𝓝 (iSup f)) := by
  obtain ⟨B, h_lub⟩ := Real.exists_isLUB (Set.range_nonempty f) h_bdd
  have h_sup : iSup f = B := h_lub.csSup_eq (Set.range_nonempty f)
  rw [h_sup]
  exact tendsto_atTop_isLUB h_mon h_lub

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has the finite limit `iInf f`. -/
theorem _root_.Real.tendsto_ciInf_of_bddBelow_antitone {f : ℕ → ℝ}
    (h_bdd : BddBelow (Set.range f)) (h_ant : Antitone f) :
    Tendsto f atTop (𝓝 (iInf f)) := by
  obtain ⟨B, h_glb⟩ := Real.exists_isGLB (Set.range_nonempty f) h_bdd
  have h_inf : iInf f = B := h_glb.csInf_eq (Set.range_nonempty f)
  rw [h_inf]
  exact tendsto_atTop_isGLB h_ant h_glb

/-- A monotone, bounded above sequence `f : ℕ → ℝ` on `Set.Ici k` has the finite
limit `sSup (f '' Set.Ici k)`. -/
theorem _root_.Real.tendsto_csSup_of_bddAbove_monotoneOn_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddAbove (f '' Set.Ici k)) (h_mon : MonotoneOn f (Set.Ici k)) :
    Tendsto f atTop (𝓝 (sSup (f '' Set.Ici k))) := by
  rw [← Set.range_add_nat_eq_image_nat_Ici] at h_bdd
  rw [← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  have h := Real.tendsto_ciSup_of_bddAbove_monotone h_bdd h_mon
  rwa [tendsto_add_atTop_iff_nat k, ← sSup_range,
    Set.range_add_nat_eq_image_nat_Ici, Set.image] at h

/-- An antitone, bounded below sequence `f : ℕ → ℝ` on `Set.Ici k` has the finite
limit `sInf (f '' Set.Ici k)`. -/
theorem _root_.Real.tendsto_csInf_of_bddBelow_antitoneOn_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddBelow (f '' Set.Ici k)) (h_ant : AntitoneOn f (Set.Ici k)) :
    Tendsto f atTop (𝓝 (sInf (f '' Set.Ici k))) := by
  rw [← Set.range_add_nat_eq_image_nat_Ici] at h_bdd
  rw [← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  have h := Real.tendsto_ciInf_of_bddBelow_antitone h_bdd h_ant
  rwa [tendsto_add_atTop_iff_nat k, ← sInf_range,
    Set.range_add_nat_eq_image_nat_Ici, Set.image] at h

/-- The limit of a monotone, bounded above sequence `f : ℕ → ℝ` is a least upper bound
of the sequence. -/
theorem _root_.Real.isLUB_limUnder_of_bddAbove_monotone  {f : ℕ → ℝ}
    (h_bdd : BddAbove (Set.range f)) (h_mon : Monotone f) :
    IsLUB (Set.range f) (limUnder atTop f) := by
  have h := Real.tendsto_ciSup_of_bddAbove_monotone h_bdd h_mon
  rw [h.limUnder_eq]
  exact isLUB_ciSup h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` is a greatest lower bound
of the sequence. -/
theorem _root_.Real.isGLB_limUnder_of_bddBelow_antitone  {f : ℕ → ℝ}
    (h_bdd : BddBelow (Set.range f)) (h_ant : Antitone f) :
    IsGLB (Set.range f) (limUnder atTop f) := by
  have h := Real.tendsto_ciInf_of_bddBelow_antitone h_bdd h_ant
  rw [h.limUnder_eq]
  exact isGLB_ciInf h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Set.Ici k` is a least
upper bound of the sequence. -/
theorem _root_.Real.isLUB_limUnder_of_bddAbove_monotoneOn_Ici  {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddAbove (f '' Set.Ici k)) (h_mon : MonotoneOn f (Set.Ici k)) :
    IsLUB (f '' Set.Ici k) (limUnder atTop f) := by
  have h := Real.tendsto_csSup_of_bddAbove_monotoneOn_Ici h_bdd h_mon
  rw [h.limUnder_eq]
  exact isLUB_csSup (Set.image_nonempty.mpr Set.nonempty_Ici) h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Set.Ici k` is a greatest
lower bound of the sequence. -/
theorem _root_.Real.isGLB_limUnder_of_bddBelow_antitoneOn_Ici  {f : ℕ → ℝ} {k : ℕ}
    (h_bdd : BddBelow (f '' Set.Ici k)) (h_ant : AntitoneOn f (Set.Ici k)) :
    IsGLB (f '' Set.Ici k) (limUnder atTop f) := by
  have h := Real.tendsto_csInf_of_bddBelow_antitoneOn_Ici h_bdd h_ant
  rw [h.limUnder_eq]
  exact isGLB_csInf (Set.image_nonempty.mpr Set.nonempty_Ici) h_bdd

end Monotone

end Real
