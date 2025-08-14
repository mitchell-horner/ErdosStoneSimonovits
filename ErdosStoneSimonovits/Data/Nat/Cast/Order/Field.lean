import Mathlib

namespace Nat

section LinearOrderedField

variable {α : Type*} [LinearOrderedField α]

theorem one_sub_one_div_cast_nonneg (n : ℕ) : 0 ≤ 1 - 1 / (n : α) := by
  rw [sub_nonneg, one_div]
  exact cast_inv_le_one n

theorem one_sub_one_div_cast_le_one (n : ℕ) : 1 - 1 / (n : α) ≤ 1 := by
  rw [sub_le_self_iff]
  exact one_div_cast_nonneg n

end LinearOrderedField

end Nat
