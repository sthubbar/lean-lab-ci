/-
A negative test of coarse averaging for the cited analytic corollary.
Source: https://arxiv.org/abs/1305.2897v4, page 3 Theorem 1.2 and Corollary 1.3,
and pages 47 and 48 Corollary 4.9. The latter bounds the Mellin averaging factor.
The closed form used here is derived from the interval weight.
This tests the coarse method only. Corollary 1.3 uses finer estimates.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.HelfgottArcs
open Real

/-- Averaging the coarse coefficient 56 alone exceeds the required coefficient 76. -/
theorem naive_cor13_coefficient_gt : (76 : ℝ) < 56 * (4 * (1 - 1 / Real.sqrt 2)) ^ 2 := by
  have hs : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hi : 1 / Real.sqrt 2 < (0.7072 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hh : (1.1712 : ℝ) < 4 * (1 - 1 / Real.sqrt 2) := by linarith
  have hsq : (1.1712 : ℝ) ^ 2 < (4 * (1 - 1 / Real.sqrt 2)) ^ 2 :=
    pow_lt_pow_left₀ hh (by norm_num) (by norm_num)
  nlinarith only [hsq]

end LeanLab.HelfgottArcs
