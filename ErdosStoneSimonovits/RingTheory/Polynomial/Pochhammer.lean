import Mathlib

section Ring

variable {R : Type*} [Ring R]

/-- `descPochhammer R n` is `0` for `0, 1, …, n-1`. -/
theorem descPochhammer_eval_coe_nat_of_lt {k n : ℕ} (h : k < n) :
    (descPochhammer R n).eval (k : R) = 0 := by
  rw [descPochhammer_eval_eq_ascPochhammer, sub_add_eq_add_sub,
    ← Nat.cast_add_one, ← neg_sub, ← Nat.cast_sub h]
  exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.sub_lt_of_pos_le k.succ_pos h)

lemma descPochhammer_eval_eq_prod_range {R : Type*} [CommRing R] (n : ℕ) (r : R) :
    (descPochhammer R n).eval r = ∏ j ∈ Finset.range n, (r - j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [descPochhammer_succ_right, ih, ← Finset.prod_range_succ]

end Ring

section StrictOrderedRing

variable {S : Type*} [StrictOrderedRing S]

/-- `descPochhammer S n` is positive on `(n-1, ∞)`. -/
theorem descPochhammer_pos {n : ℕ} {s : S} (h : n - 1 < s) :
    0 < (descPochhammer S n).eval s := by
  rw [← sub_pos, ← sub_add] at h
  rw [descPochhammer_eval_eq_ascPochhammer]
  exact ascPochhammer_pos n (s - n + 1) h

/-- `descPochhammer S n` is nonnegative on `[n-1, ∞)`. -/
theorem descPochhammer_nonneg {n : ℕ} {s : S} (h : n - 1 ≤ s) :
    0 ≤ (descPochhammer S n).eval s := by
  rcases eq_or_lt_of_le h with heq | h
  · rw [← heq, descPochhammer_eval_eq_ascPochhammer,
      sub_sub_cancel_left, neg_add_cancel, ascPochhammer_eval_zero]
    positivity
  · exact (descPochhammer_pos h).le

/-- `descPochhammer S n` is at least `(s-n+1)^n` on `[n-1, ∞)`. -/
theorem pow_le_descPochhammer_eval {n : ℕ} {s : S} (h : n - 1 ≤ s) :
    (s - n + 1)^n ≤ (descPochhammer S n).eval s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_sub_cancel_right, ← sub_nonneg] at h
    have hsub1 : n - 1 ≤ s := (sub_le_self (n : S) zero_le_one).trans (le_of_sub_nonneg h)
    rw [pow_succ, descPochhammer_succ_eval, Nat.cast_add_one, sub_add, add_sub_cancel_right]
    apply mul_le_mul _ le_rfl h (descPochhammer_nonneg hsub1)
    exact (ih hsub1).trans' <| pow_le_pow_left₀ h (le_add_of_nonneg_right zero_le_one) n

/-- `descPochhammer S n` is monotone on `[n-1, ∞)`. -/
theorem monotoneOn_descPochhammer_eval (n : ℕ) :
    MonotoneOn (descPochhammer S n).eval (Set.Ici (n - 1 : S)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ici, Nat.cast_add_one, add_sub_cancel_right] at ha hb
    have ha_sub1 : n - 1 ≤ a := (sub_le_self (n : S) zero_le_one).trans ha
    have hb_sub1 : n - 1 ≤ b := (sub_le_self (n : S) zero_le_one).trans hb
    simp_rw [descPochhammer_succ_eval]
    exact mul_le_mul (ih ha_sub1 hb_sub1 hab) (sub_le_sub_right hab (n : S))
      (sub_nonneg_of_le ha) (descPochhammer_nonneg hb_sub1)

end StrictOrderedRing
