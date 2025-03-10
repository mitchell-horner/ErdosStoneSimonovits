import Mathlib

namespace Nat

variable {m n : ℕ}

lemma sub_mod_eq_mul_div : m - (m % n) = n * (m / n) := by
  rw [Nat.sub_eq_iff_eq_add (Nat.mod_le _ _), Nat.add_comm, mod_add_div]

-- lemma div_eq_sub_mod_div : m / n = (m - m % n) / n := by
--   obtain rfl | hn := n.eq_zero_or_pos
--   · rw [Nat.div_zero, Nat.div_zero]
--   · rw [sub_mod_eq_mul_div, mul_div_right _ hn]

end Nat
