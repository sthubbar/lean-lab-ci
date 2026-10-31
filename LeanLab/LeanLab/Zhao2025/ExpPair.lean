import Mathlib

/-!
The elementary exponential pair in display 2.23 increases with lambda.
Source: Zhao 2025, displays 2.23 and 2.25, pages 6 and 7.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The pair is a positive multiple of cosh on nonnegative arguments. -/
theorem exp_pair_monotone (l L l0 u : ℝ) (hl : 0 ≤ l) (h0 : 0 ≤ l0)
    (hL : l ≤ L) (hu : 0 ≤ u) :
    Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u) ≤
      Real.exp (L * u) + Real.exp (-(L + 2 * l0) * u) := by
  have heq (r : ℝ) : Real.exp (r * u) + Real.exp (-(r + 2 * l0) * u) =
      2 * Real.exp (-l0 * u) * Real.cosh ((r + l0) * u) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-l0 * u) * Real.exp ((r + l0) * u) = Real.exp (r * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-l0 * u) * Real.exp (-((r + l0) * u)) =
        Real.exp (-(r + 2 * l0) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.exp (-l0 * u) * Real.exp ((r + l0) * u) +
          Real.exp (-l0 * u) * Real.exp (-((r + l0) * u)) := by rw [h1, h2]
      _ = _ := by ring
  rw [heq l, heq L]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hL0 : 0 ≤ L := hl.trans hL
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ (l + l0) * u),
    abs_of_nonneg (by positivity : 0 ≤ (L + l0) * u)]
  exact mul_le_mul_of_nonneg_right (by linarith : l + l0 ≤ L + l0) hu

#print axioms exp_pair_monotone

end LeanLab.Zhao2025.Task56
