import Mathlib

/-
AI wrote this Lean code. Binary Goldbach is open.
This records a failed route to the P0099 page 11 Table 1 interval.
The factor two interval bound alone does not imply the printed short interval bound.
-/

namespace LeanLab.Ternary78.Paper104

/-- A negative order calculation for the attempted Bertrand route.
This concerns candidate locations only and makes no primality assertion. -/
theorem coarse_interval_not_sufficient :
    ¬ ∀ x p : ℝ, (10 : ℝ) ^ 20 ≤ x → x / 2 < p → p ≤ x →
      x * (1 - 1 / 81353847) < p := by
  intro h
  have hbad := h ((10 : ℝ) ^ 20) ((10 : ℝ) ^ 20 / 2 + 1)
    le_rfl (by norm_num) (by norm_num)
  norm_num at hbad

#print axioms coarse_interval_not_sufficient

end LeanLab.Ternary78.Paper104
