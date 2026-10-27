/-
Tao 2012, page 16, equation 4.3 needs the cited coefficient 1.04.
Mathlib Chebyshev.psi_le has main coefficient log 4. This route is too weak.
CODEX task137. AI wrote this Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Tao2012.InputAudit137
open Real

/-- The right side of Mathlib Chebyshev.psi_le exceeds the target in Tao equation 4.3
for every x at least one. This is a negative result about that proof route. -/
theorem coarse_psi_rhs_exceeds {x : ℝ} (hx : 1 ≤ x) :
    1.04 * x < log 4 * x + 2 * sqrt x * log x := by
  have hl : (1.04 : ℝ) < log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    norm_num at *
    linarith
  have hx0 : 0 < x := by linarith
  have hmain := mul_lt_mul_of_pos_right hl hx0
  have htail : 0 ≤ 2 * sqrt x * log x := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (log_nonneg hx)
  linarith

end LeanLab.Tao2012.InputAudit137
