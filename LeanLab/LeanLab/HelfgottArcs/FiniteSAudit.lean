/-
A negative test of the phase-free bound as a route to the minor arc target.
Source: https://arxiv.org/abs/1205.5252v4, Main Theorem, pages 1 to 3.
This is a limitation of the elementary triangle estimate, not a paper error claim.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FiniteS
import LeanLab.HelfgottArcs.MinorMain

namespace LeanLab.HelfgottArcs
open Real

/-- At the printed threshold, the large denominator minor arc bound is below x. -/
theorem minorBoundLarge_x0_lt_x0 : minorBoundLarge 2.16e20 < (2.16e20 : ℝ) := by
  have hbase : (2.16e20 : ℝ) ≤ (2500 : ℝ) ^ (6 : ℕ) := by norm_num
  have h5 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2.16e20) hbase
    (by norm_num : (0 : ℝ) ≤ 5 / 6)
  have h4 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2.16e20) hbase
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have he5 : ((2500 : ℝ) ^ (6 : ℕ)) ^ ((5 : ℝ) / 6) = (2500 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have he4 : ((2500 : ℝ) ^ (6 : ℕ)) ^ ((2 : ℝ) / 3) = (2500 : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [he5] at h5
  rw [he4] at h4
  have hl := MinorMain.L_bounds
  have hp : log (2.16e20 : ℝ) ^ ((3 : ℝ) / 2) ≤ (47 : ℝ) ^ (2 : ℕ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ log (2.16e20 : ℝ) by linarith [hl.1]) (by norm_num : (3 : ℝ) / 2 ≤ 2)
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] at hpow
    exact hpow.trans (pow_le_pow_left₀ (by linarith [hl.1]) hl.2.le 2)
  unfold minorBoundLarge
  calc _ ≤ 0.2727 * (2500 : ℝ) ^ (5 : ℕ) * (47 : ℝ) ^ (2 : ℕ) +
      1218 * (2500 : ℝ) ^ (4 : ℕ) * 47 := by
        gcongr
        exact hl.2.le
    _ < (2.16e20 : ℝ) := by norm_num

/-- The coarse triangle bound is already too large at the minor arc threshold. -/
theorem coarse_bound_exceeds_minor_at_x0 :
    minorBoundLarge 2.16e20 <
      (Nat.ceil (2.16e20 : ℝ) : ℝ) * (4 * log 2 * log (2.16e20 : ℝ)) := by
  have hl := MinorMain.L_bounds.1
  have htwo := Real.log_two_gt_d9
  have hm : 1 < 4 * log 2 * log (2.16e20 : ℝ) := by nlinarith
  have hc := Nat.le_ceil (2.16e20 : ℝ)
  have hx : (2.16e20 : ℝ) < (2.16e20 : ℝ) * (4 * log 2 * log (2.16e20 : ℝ)) := by
    nlinarith
  have hcoarse := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 4 * log 2 * log (2.16e20 : ℝ) by linarith)
  exact minorBoundLarge_x0_lt_x0.trans (hx.trans_le hcoarse)

end LeanLab.HelfgottArcs
