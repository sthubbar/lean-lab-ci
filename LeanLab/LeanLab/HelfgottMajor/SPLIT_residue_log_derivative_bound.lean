import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Split of the open logarithmic derivative bound of the residue in
`LeanLab.HelfgottMajor.Gaussian123Base`, displays 4.18 to 4.22 and the display before 4.23,
pages 36 and 37. The sealed statement bounds
`log (2 * π / q) + γ - L'(1, χ)/L(1, χ)` by `3 log q + 15.289` for a primitive character modulo
`q` with `q` not equal to `1`. The four leaves are the quotient itself, the scalar logarithm,
the numerical constant of page 37, and the conductor reduction to `3 ≤ q`;
`residue_log_derivative_bound_split` assembles them with the triangle inequality.
The namespace is the target's, so the names the rest of the lab refers to are unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- LEAF: step 1 of 4, the quotient on its own. Pages 36 and 37, displays 4.18 to 4.22 and the
display before 4.23: for a primitive character modulo `q` with `q` not equal to `1`, the norm of
`L'(1, χ)/L(1, χ)` is at most `2 log q + 15.07017`. The scalar logarithm of the sealed statement
is absent from this inequality; it is one of the two terms of the residue. -/
theorem log_derivative_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      2 * log q + 15.07017 := by
  sorry

/-- LEAF: step 2 of 4, the scalar logarithm. Page 37: for a real `q` at least `3`, the absolute
value of `log (2π/q) + γ` is at most `log q + (γ + log 2π - log 9)`. This is the elementary
comparison of `2π` with `q ^ 2` and of `9` with `q ^ 2`, losing one power of `log q` and no
more. No character and no `L` function occurs in it. -/
theorem log_two_pi_div_add_gamma_abs_le (q : ℝ) (hq : 3 ≤ q) :
    |log (2 * π / q) + eulerMascheroniConstant| ≤
      log q + (eulerMascheroniConstant + log (2 * π) - log 9) := by
  sorry

/-- LEAF: step 3 of 4, the numerical constant of page 37: `γ + log 2π - log 9 + 15.07017` is at
most `15.289`. Decimal arithmetic with the bounds `γ < 0.57738` and `2π/9 > exp (-0.359)`, and no
variable at all; the whole margin between the two constants lives here. -/
theorem page37_constant_budget :
    eulerMascheroniConstant + log (2 * π) - log 9 + 15.07017 ≤ 15.289 := by
  sorry

/-- LEAF: step 4 of 4, the conductor reduction. Page 37 notes that there is no primitive
character modulo `2`, so a primitive character modulo `q` with `q` not equal to `1` has `q` at
least `3`. This is the hypothesis the scalar estimate of step 2 needs, and it is arithmetic about
the conductor alone. -/
theorem three_le_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : 3 ≤ q := by
  sorry

/-- The sealed statement of `LeanLab.HelfgottMajor.Gaussian123Base`, proved from the four leaves
above by the triangle inequality and the arithmetic of page 37. -/
theorem residue_log_derivative_bound_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    ‖((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      3 * log q + 15.289 := by
  have h3 := three_le_conductor χ hχ hq
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have hscal := log_two_pi_div_add_gamma_abs_le (q : ℝ) hq3
  have hquot := log_derivative_norm_le χ hχ hq
  have hconst := page37_constant_budget
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

end LeanLab.HelfgottMajor.SplitGaussian123
