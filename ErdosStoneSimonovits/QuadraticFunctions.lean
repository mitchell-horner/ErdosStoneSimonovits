import Mathlib

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
