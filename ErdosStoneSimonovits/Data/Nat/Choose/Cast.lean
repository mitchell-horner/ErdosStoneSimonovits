import Mathlib

open Nat

variable (K : Type*)

namespace Nat

section DivisionRing

variable [DivisionRing K] [CharZero K]

theorem cast_choose_eq_descPochhammer_div (a b : ℕ) :
    (a.choose b : K) = (descPochhammer K b).eval ↑a / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) ≠ 0), ← cast_mul,
    mul_comm, ← descFactorial_eq_factorial_mul_choose, descPochhammer_eval_eq_descFactorial]

end DivisionRing

end Nat
