import Mathlib

section QuadraticFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The linear function `x ↦ a * x + b` is differentiable. -/
lemma differentiable_linear (a b : 𝕜) :
    Differentiable 𝕜 (fun x ↦ a*x+b) := by
  conv_rhs =>
    intro x
    rw [←pow_one x]
  exact ((differentiable_const a).mul (differentiable_pow 1)).add
    (differentiable_const b)

/-- The linear function `x ↦ a * x + b` is continuous. -/
lemma continuous_linear (a b : 𝕜) :
  Continuous (fun x ↦ a*x+b) := (differentiable_linear a b).continuous

/-- The derivative of the function `x ↦ a * x + b` is `a`. -/
lemma deriv_linear (x a b : 𝕜) :
    deriv (fun x ↦ a*x+b) x = a := by
  conv_lhs =>
    lhs; intro x
    rw [←pow_one x]
  rw [deriv_add, deriv_const_mul_field, deriv_pow 1, deriv_const x b]
  ring_nf
  all_goals
    apply Differentiable.differentiableAt
  exact (differentiable_const a).mul (differentiable_pow 1)
  exact differentiable_const b

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is differentiable. -/
lemma differentiable_quadratic (a b c : 𝕜) :
    Differentiable 𝕜 (fun x ↦ a*x^2+b*x+c) := by
  conv_rhs =>
    intro x
    rw [add_assoc]
  exact ((differentiable_const a).mul (differentiable_pow 2)).add
    (differentiable_linear b c)

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is continuous. -/
lemma continuous_quadratic (a b c : 𝕜) :
  Continuous (fun x ↦ a*x^2+b*x+c) :=
    (differentiable_quadratic a b c).continuous

/-- The derivative of the quadratic function `x ↦ a * x^2 + b * x + c` is
`x ↦ 2 * a * x + b`. -/
lemma deriv_quadratic (x a b c : 𝕜) :
    deriv (fun x ↦ a*x^2+b*x+c) x = (fun x ↦ 2*a*x+b) x := by
  conv_lhs =>
    lhs; intro x
    rw [add_assoc]
  rw [deriv_add, deriv_const_mul_field, deriv_pow 2, deriv_linear x b c]
  ring_nf
  all_goals
    apply Differentiable.differentiableAt
  exact (differentiable_const a).mul (differentiable_pow 2)
  exact differentiable_linear b c

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is strictly monotonic on
`[-b/(2*a), ∞)` if the leading coefficent is positive. -/
lemma quadratic_strictMonoOn_of_leadingCoeff_pos (a b c : ℝ) (ha : 0 < a) :
    StrictMonoOn (fun x ↦ a*x^2+b*x+c) (Set.Ici (-b/(2*a))) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuous_quadratic a b c).continuousOn
  intro x hx
  rw [deriv_quadratic]
  rwa [interior_Ici, Set.mem_Ioi, div_lt_iff (mul_pos two_pos ha),
    ←sub_pos, sub_neg_eq_add, mul_comm] at hx

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is strictly antitonic on
`(-∞, -b/(2*a)]` if the leading coefficent is positive. -/
lemma quadratic_strictAntiOn_of_leadingCoeff_pos (a b c : ℝ) (ha : 0 < a) :
    StrictAntiOn (fun x ↦ a*x^2+b*x+c) (Set.Iic (-b/(2*a))) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _)
    (continuous_quadratic a b c).continuousOn
  intro x hx
  rw [deriv_quadratic]
  rwa [interior_Iic, Set.mem_Iio, lt_div_iff (mul_pos two_pos ha),
    ←sub_neg, sub_neg_eq_add, mul_comm] at hx

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is strictly antitonic on
`[-b/(2*a), ∞)` if the leading coefficent is positive. -/
lemma quadratic_strictAntiOn_of_leadingCoeff_neg (a b c : ℝ) (ha : a < 0) :
    StrictAntiOn (fun x ↦ a*x^2+b*x+c) (Set.Ici (-b/(2*a))) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (continuous_quadratic a b c).continuousOn
  intro x hx
  rw [deriv_quadratic]
  rwa [interior_Ici, Set.mem_Ioi,
    div_lt_iff_of_neg (mul_neg_of_pos_of_neg two_pos ha),
    ←sub_neg, sub_neg_eq_add, mul_comm] at hx

/-- The quadratic function `x ↦ a * x^2 + b * x + c` is strictly monotonic on
`(-∞, -b/(2*a)]` if the leading coefficent is negative. -/
lemma quadratic_strictMonoOn_of_leadingCoeff_neg (a b c : ℝ) (ha : a < 0) :
    StrictMonoOn (fun x ↦ a*x^2+b*x+c) (Set.Iic (-b/(2*a))) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
    (continuous_quadratic a b c).continuousOn
  intro x hx
  rw [deriv_quadratic]
  rwa [interior_Iic, Set.mem_Iio,
    lt_div_iff_of_neg (mul_neg_of_pos_of_neg two_pos ha),
    ←sub_pos, sub_neg_eq_add, mul_comm] at hx

end QuadraticFunctions

section DescPochhammer

variable {R : Type*} [OrderedCommRing R]

lemma descPochhammer_eval_eq_prod_range (k : ℕ) (x : R) :
    (descPochhammer R k).eval x = ∏ j ∈ Finset.range k, (x-j) := by
  induction k with
  | zero =>
    rw [descPochhammer_zero, Polynomial.eval_one,
      Finset.range_zero, Finset.prod_empty]
  | succ k ih =>
    rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, Finset.prod_range_succ, ih]

/-- `descPochhammer R k` is `0` for `0, 1, …, k-1`. -/
theorem descPochhammer_eval_natCast_eq_zero
    {k : ℕ} (hk : k ≥ 1) (h : n ≤ k-1) :
    (descPochhammer R k).eval (n : R) = 0 := by
  have h' : n ∈ Finset.range k := by
    rw [ge_iff_le, Nat.one_le_iff_ne_zero] at hk
    rw [Finset.mem_range]
    exact lt_of_le_of_lt h (Nat.pred_lt hk)
  simp_rw [descPochhammer_eval_eq_prod_range]
  exact Finset.prod_eq_zero h' (sub_self (n : R))

/-- `descPochhammer R k` is at least `(x-k+1)^k` for `x ∈ [k-1, ∞)`. -/
lemma sub_pow_le_descPochhammer_eval [CharZero R]
    {k : ℕ} (hk : k ≥ 1) {x : R} (h : k-1 ≤ x) :
    (x-k+1)^k ≤ (descPochhammer R k).eval x := by
  simp_rw [descPochhammer_eval_eq_prod_range]
  conv_lhs =>
    rhs; rw [←Finset.card_range k]
  rw [←Finset.prod_const]
  apply Finset.prod_le_prod
  . intro i hi
    rwa [←sub_nonneg, ←sub_add] at h
  . intro i hi
    rw [sub_add, ←Nat.cast_pred hk, sub_le_sub_iff_left, Nat.cast_le]
    rw [Finset.mem_range] at hi
    exact Nat.le_pred_of_lt hi

/-- `descPochhammer R k` is nonnegative on `[k-1, ∞)`. -/
theorem descPochhammer_eval_nonneg [CharZero R]
    (k : ℕ) {x : R} (h : k-1 ≤ x) :
    0 ≤ (descPochhammer R k).eval x := by
  by_cases hk : k = 0
  . simp_rw [hk, descPochhammer_zero, Polynomial.eval_one]
    exact zero_le_one
  . rw [←Ne, ←Nat.one_le_iff_ne_zero] at hk
    rw [descPochhammer_eval_eq_prod_range]
    apply Finset.prod_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    have hi' : i ≤ (k : R)-1 := by
      rw [←Nat.cast_pred hk, Nat.cast_le]
      exact Nat.le_pred_of_lt hi
    apply sub_nonneg_of_le
    exact hi'.trans h

/-- `descPochhammer R k` is monotone on `[k-1, ∞)`. -/
theorem MonotoneOn.descPochhammer_eval [CharZero R] (k : ℕ) :
    MonotoneOn (descPochhammer R k).eval (Set.Ici (k-1 : R)) := by
  by_cases hk : k = 0
  . simp_rw [hk, Nat.cast_zero, zero_sub, descPochhammer_zero,
      Polynomial.eval_one]
    exact monotoneOn_const
  . rw [←Ne, ←Nat.one_le_iff_ne_zero] at hk
    intro a ha b _ hab
    simp_rw [descPochhammer_eval_eq_prod_range]
    apply Finset.prod_le_prod
    . intro i hi
      rw [Finset.mem_range] at hi
      apply sub_nonneg_of_le
      have hi' : (i : R) ≤ (k : R)-1 := by
        rw [←Nat.cast_pred hk, Nat.cast_le]
        exact Nat.le_pred_of_lt hi
      exact hi'.trans ha
    . intro i _
      exact sub_le_sub_right hab _

theorem Continuous.descPochhammer_eval :
    Continuous (descPochhammer ℝ k).eval := by
  simp_rw [descPochhammer_eval_eq_prod_range]
  apply continuous_finset_prod
  intro i _
  have h := continuous_linear 1 (-i : ℝ)
  conv_rhs at h =>
    intro x
    rw [one_mul, ←sub_eq_add_neg]
  exact h

theorem Differentiable.descPochhammer_eval :
    Differentiable ℝ (descPochhammer ℝ k).eval := by
  simp_rw [descPochhammer_eval_eq_prod_range]
  apply Differentiable.finset_prod
  intro i _
  have h := differentiable_linear 1 (-i : ℝ)
  conv_rhs at h =>
    intro x
    rw [one_mul, ←sub_eq_add_neg]
  exact h

lemma deriv_descPochhammer_eval :
    deriv (descPochhammer ℝ k).eval x
      = ∑ i ∈ Finset.range k, (∏ j ∈ (Finset.range k).erase i, (x-j)) := by
  simp_rw [descPochhammer_eval_eq_prod_range]
  rw [deriv_finset_prod]
  simp only [differentiableAt_id', differentiableAt_const, deriv_sub,
    deriv_id'', deriv_const', sub_zero, smul_eq_mul, mul_one]
  intro i _
  have h := differentiable_linear 1 (-i : ℝ)
  conv_rhs at h =>
    intro x
    rw [one_mul, ←sub_eq_add_neg]
  exact h.differentiableAt

/-- `descPochhammer ℝ k` is convex on `[k-1, ∞)`. -/
theorem ConvexOn.descPochhammer_eval (k : ℕ):
    ConvexOn ℝ (Set.Ici (k-1 : ℝ)) (descPochhammer ℝ k).eval := by
  by_cases hk : k = 0
  . simp_rw [hk, Nat.cast_zero, zero_sub, descPochhammer_zero,
      Polynomial.eval_one]
    exact convexOn_const 1 (convex_Ici (-1 : ℝ))
  . rw [←Ne, ←Nat.one_le_iff_ne_zero] at hk
    apply MonotoneOn.convexOn_of_deriv (convex_Ici (k-1 : ℝ))
      Continuous.descPochhammer_eval.continuousOn
      Differentiable.descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [Set.mem_Ioi] at hx hy
    simp_rw [deriv_descPochhammer_eval]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    apply Finset.prod_le_prod
    . intro i' hi'
      rw [Finset.mem_erase, Finset.mem_range] at hi'
      apply sub_nonneg_of_le
      have hi'' : i' ≤ (k : ℝ)-1 := by
        rw [←Nat.cast_pred hk, Nat.cast_le]
        exact Nat.le_pred_of_lt hi'.2
      exact le_of_lt (lt_of_le_of_lt hi'' hx)
    . intro i' _
      rw [sub_le_sub_iff_right]
      exact hxy

/-- The continuous analogue of `n.choose k` using `descPochhammer ℝ k` is
convex on the real line. -/
lemma ConvexOn.ite_descPochhammer_eval {k : ℕ} (hk : k ≥ 1) :
    ConvexOn ℝ Set.univ (fun (x : ℝ) ↦ if x ≥ k-1 then
      (descPochhammer ℝ k).eval x else 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hx : x ≥ k-1 <;> by_cases hy : y ≥ k-1
  all_goals simp only [hx, hy, ↓reduceIte,
      smul_eq_mul, mul_zero, add_zero, zero_add]
  . have haxby : a*x+b*y ≥ k-1 := by
      trans min x y
      . exact Convex.min_le_combo x y ha hb hab
      . exact le_min hx hy
    simp only [haxby, ↓reduceIte]
    exact (ConvexOn.descPochhammer_eval k).2 hx hy ha hb hab
  . push_neg at hy
    have haxby' : a*x+b*y ≤ a*x+b*(k-1) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    by_cases haxby : a*x+b*y ≥ k-1
    all_goals simp only [haxby, ↓reduceIte]
    . trans (descPochhammer ℝ k).eval (a*x+b*(k-1))
      . apply MonotoneOn.descPochhammer_eval
          k haxby (haxby'.trans' haxby) haxby'
      . conv_rhs =>
          rw [←add_zero (a*_), ←mul_zero b,
            ←descPochhammer_eval_natCast_eq_zero hk (le_refl (k-1)),
            Nat.cast_pred hk]
        exact (ConvexOn.descPochhammer_eval k).2
          hx (le_refl (k-1 : ℝ)) ha hb hab
    . exact mul_nonneg ha (descPochhammer_eval_nonneg k hx)
  . push_neg at hx
    have haxby' : a*x+b*y ≤ a*(k-1)+b*y := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left (le_of_lt hx) ha
    by_cases haxby : a*x+b*y ≥ k-1
    all_goals simp only [haxby, ↓reduceIte]
    . trans (descPochhammer ℝ k).eval (a*(k-1)+b*y)
      . apply MonotoneOn.descPochhammer_eval
          k haxby (haxby'.trans' haxby) haxby'
      . conv_rhs =>
          rw [←zero_add (b*_), ←mul_zero a,
            ←descPochhammer_eval_natCast_eq_zero hk (le_refl (k-1)),
            Nat.cast_pred hk]
        exact (ConvexOn.descPochhammer_eval k).2
          (le_refl (k-1 : ℝ)) hy ha hb hab
    . exact mul_nonneg hb (descPochhammer_eval_nonneg k hy)
  . push_neg at hx hy
    have haxby : a*x+b*y ≤ k-1 := by
      trans max x y
      . exact Convex.combo_le_max x y ha hb hab
      . exact max_le (le_of_lt hx) (le_of_lt hy)
    rw [le_iff_eq_or_lt] at haxby
    cases haxby with
    | inl haxby =>
      have haxby' := ge_of_eq haxby
      rw [←Nat.cast_pred hk] at haxby
      simp [haxby', ↓reduceIte, haxby,
        descPochhammer_eval_natCast_eq_zero hk]
    | inr haxby =>
      rw [←not_le] at haxby
      simp [haxby, ↓reduceIte]

/-- The continuous analogue of `n.choose k` using `descPochhammer ℝ k`. -/
theorem choose_eq_ite_descPochhammer_eval_div_factorial (n k : ℕ) :
    n.choose k = (if (n : ℝ) ≥ k-1 then
        (descPochhammer ℝ k).eval (n : ℝ) else 0) / k.factorial := by
  by_cases hk : k = 0
  . have h : (n : ℝ) ≥ k-1 := by
      rw [hk, Nat.cast_zero, zero_sub, ge_iff_le,
        neg_le_iff_add_nonneg, ←Nat.cast_add_one]
      exact Nat.cast_nonneg _
    simp only [h, ↓reduceIte]
    rw [hk, Nat.choose_zero_right, descPochhammer_zero,
      Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one, one_div_one]
  . rw [←Ne, ←Nat.one_le_iff_ne_zero] at hk
    by_cases h : (n : ℝ) ≥ k-1
    all_goals simp only [h, ↓reduceIte]
    . rw [←Nat.cast_pred hk, ge_iff_le, Nat.cast_le, le_iff_lt_or_eq] at h
      cases h with
      | inl h =>
        have h' : n ≥ k := Nat.le_of_pred_lt h
        rw [descPochhammer_eval_eq_descFactorial, Nat.cast_choose ℝ h',
          mul_comm, ←div_div, ←Nat.cast_div, ←Nat.descFactorial_eq_div h']
        . apply Nat.factorial_dvd_factorial
          exact Nat.sub_le n k
        . rw [Nat.cast_ne_zero]
          exact Nat.factorial_ne_zero (n-k)
      | inr h =>
        rw [←h, descPochhammer_eval_natCast_eq_zero hk (le_refl (k-1)),
          zero_div, Nat.cast_eq_zero, Nat.choose_eq_zero_iff]
        exact Nat.pred_lt_of_lt hk
    . push_neg at h
      rw [←Nat.cast_pred hk, Nat.cast_lt] at h
      rw [zero_div, Nat.cast_eq_zero, Nat.choose_eq_zero_iff]
      exact h.trans (Nat.pred_lt_of_lt hk)

/-- **Jensen's inequality** for `Nat.choose`. -/
theorem descPochhammer_eval_le_sum_choose
    {k : ℕ} (hk : k ≥ 1) {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (h_le : ∑ i ∈ t, (w i * p i) ≥ k-1):
    (descPochhammer ℝ k).eval (∑ i ∈ t, w i * p i) / k.factorial
      ≤ (∑ i ∈ t, w i * (p i).choose k) := by
  conv_rhs =>
    rhs; intro a
    rw [choose_eq_ite_descPochhammer_eval_div_factorial, mul_div, ←smul_eq_mul]
  rw [←Finset.sum_div,
    div_le_div_right (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  let f : ℝ → ℝ := fun (x : ℝ) ↦ if x ≥ k-1 then
    (descPochhammer ℝ k).eval x else 0
  suffices h_jensen : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) by
    simpa only [smul_eq_mul, f, h_le, ↓reduceIte] using h_jensen
  exact ConvexOn.map_sum_le
    (ConvexOn.ite_descPochhammer_eval hk) h₀ h₁ (by simp)

end DescPochhammer
