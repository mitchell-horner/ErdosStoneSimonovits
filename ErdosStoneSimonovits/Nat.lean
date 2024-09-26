import Mathlib

open Topology Asymptotics

variable {R : Type*} [LinearOrderedField R]

/-- `1` divided by a natural number `n > 1` is less than `1`. -/
lemma Nat.one_div_cast_lt_one {n : ℕ} (hn : 1 < n) :
    1/(n : R) < 1 := by
  conv_rhs =>
    rw [←one_div_one]
  apply one_div_lt_one_div_of_lt zero_lt_one
  rw [←Nat.cast_one, Nat.cast_lt]
  exact hn

lemma Nat.one_sub_one_div_cast_pos {n : ℕ} (hn : 1 < n) :
    0 < 1-1/(n : R) := by
  rw [sub_pos]
  exact Nat.one_div_cast_lt_one hn

lemma Nat.one_sub_one_div_cast_lt_one
    {n : ℕ} (hn : 0 < n) : 1-1/(n : R) < 1 := by
  rw [sub_lt_self_iff, div_pos_iff]
  left
  refine ⟨zero_lt_one, ?_⟩
  rw [Nat.cast_pos]
  exact hn

/-- `1` divided by a natural number `n` is at most `1`. -/
lemma Nat.one_div_cast_le_one (n : ℕ) : 1/(n : R) ≤ 1 := by
  by_cases h : n = 0
  . rw [h]
    field_simp
  . conv_rhs =>
      rw [←one_div_one]
    apply one_div_le_one_div_of_le zero_lt_one
    rw [←Nat.cast_one, Nat.cast_le, Nat.one_le_iff_ne_zero]
    exact h

lemma Nat.one_sub_one_div_cast_nonneg (n : ℕ) : 0 ≤ 1-1/(n : R) := by
  rw [sub_nonneg]
  exact Nat.one_div_cast_le_one n

lemma Nat.one_sub_one_div_cast_le_one (n : ℕ) : 1-1/(n : R) ≤ 1 := by
  rw [sub_le_self_iff, div_nonneg_iff]
  left
  exact ⟨zero_le_one, Nat.cast_nonneg _⟩

/-- The multiplication of the floor division is equal to the subtraction of the
modulus. -/
lemma Nat.mul_div_eq_sub_mod (a b : ℕ) : b * (a / b) = a - (a % b) := by
  rw [eq_tsub_iff_add_eq_of_le, Nat.div_add_mod]
  exact Nat.mod_le _ _

/-- `n` choose `2` is big-Θ `n^2`. -/
lemma Nat.isTheta_choose_two :
    (fun (n : ℕ) ↦ (n.choose 2 : ℝ))
      =Θ[Filter.atTop] (fun (n : ℕ) ↦ (n^2 : ℝ)) := by
  conv_lhs =>
    intro n
    rw [Nat.cast_choose_two, mul_sub, ←pow_two, mul_one, sub_div,
      sub_eq_add_neg, add_comm]
  apply IsLittleO.add_isTheta
  . rw [isLittleO_iff_tendsto]
    convert tendsto_const_div_atTop_nhds_zero_nat (-1/2) using 1
    ext n
    by_cases hn : (n : ℝ) = 0
    . rw [hn]
      ring_nf
    . field_simp [hn]
      ring_nf
    intro n hn
    field_simp at hn ⊢
    exact hn
  . rw [←isTheta_const_mul_left two_ne_zero]
    conv_lhs =>
      intro n
      rw [mul_div_cancel₀ _ two_ne_zero]
    rfl
