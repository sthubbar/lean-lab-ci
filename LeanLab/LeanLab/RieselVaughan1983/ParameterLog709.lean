import LeanLab.RieselVaughan1983.Parameter709

/-!
The exact evaluation of k at the logarithmic trial parameters on Schoenfeld page 345.
The source uses c equal to 2 or 5 in equation 7.29.
This identity does not assert the numerical localization of the selected root.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.RieselVaughan1983.Task709

/-- The displayed evaluation of k following equation 7.29 on page 345.
The source coefficients 2 and 5 are included in the positive parameter c. -/
theorem schoenfeldK_at_log_parameter (X c d : ℝ) (hX : 0 < X) (hc : 0 < c)
    (hv : 0 < 1 - log (17 * X / (c * Real.pi)) / (2 * X)) :
    let v := 1 - log (17 * X / (c * Real.pi)) / (2 * X)
    schoenfeldK X d v = c / 2 * sqrt (schoenfeldH X d v) *
      exp (-(log (17 * X / (c * Real.pi))) ^ 2 / (4 * v * X)) := by
  let q : ℝ := 17 * X / (c * Real.pi)
  let v : ℝ := 1 - log q / (2 * X)
  have hq : 0 < q := by dsimp [q]; positivity
  have hv0 : 0 < v := hv
  have hone : 1 - v = log q / (2 * X) := by dsimp [v]; ring
  have hfirst : -2 * X * (1 - v) = -log q := by
    rw [hone]
    field_simp [hX.ne']
  have hlast : -X * (1 - v) ^ 2 / v = -(log q) ^ 2 / (4 * v * X) := by
    rw [hone]
    field_simp [hX.ne', hv0.ne']
    ring
  have hcoef : 17 * X / (2 * Real.pi) * q⁻¹ = c / 2 := by
    dsimp [q]
    field_simp [hX.ne', hc.ne', Real.pi_ne_zero]
  change schoenfeldK X d v = c / 2 * sqrt (schoenfeldH X d v) *
    exp (-(log q) ^ 2 / (4 * v * X))
  unfold schoenfeldK
  rw [hfirst, exp_neg, exp_log hq, hlast]
  calc
    _ = (17 * X / (2 * Real.pi) * q⁻¹) * sqrt (schoenfeldH X d v) *
        exp (-(log q) ^ 2 / (4 * v * X)) := by ring
    _ = _ := by rw [hcoef]

end LeanLab.RieselVaughan1983.Task709
