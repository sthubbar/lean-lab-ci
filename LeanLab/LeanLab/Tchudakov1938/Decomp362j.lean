/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362j
open Real
set_option maxHeartbeats 400000

/-- LEAF. P0064, page 34, inequality 24. Substitute zeta equal to xi to power eight thirds. -/
theorem zeta_neg_third (xi : ℝ) (hxi : 0 ≤ xi) :
    (xi ^ (8 / 3 : ℝ)) ^ (-1 / 3 : ℝ) = xi ^ (-8 / 9 : ℝ) := by
  rw [← Real.rpow_mul hxi]
  norm_num

/-- P0064, page 35, final display in the Lemma 14 proof. The logarithmic cube is absorbed by the surplus power of xi. -/
theorem lemma14_log_absorption (M x n : ℝ) (hM : 0 < M) (hx : Real.exp 1 ≤ x)
    (hn : 1 ≤ n) (hnx : n ≤ x) :
    (Real.log n)^3 * (Real.log x ^ (M + 6)) ^ (-16 / 9 : ℝ) ≤
      (Real.log x ^ (M + 6)) ^ (-1 : ℝ) := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlnx : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlog : 0 < Real.log x := by linarith
  have hexp : (3 : ℝ) ≤ (M + 6) * (7 / 9 : ℝ) := by linarith
  have hpow : (Real.log n)^3 ≤ Real.log x ^ ((M + 6) * (7 / 9 : ℝ)) := by
    calc
      (Real.log n)^3 ≤ (Real.log x)^3 := pow_le_pow_left₀ hln0 hlnx 3
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hlx hexp
  calc
    _ ≤ Real.log x ^ ((M + 6) * (7 / 9 : ℝ)) *
        (Real.log x ^ (M + 6)) ^ (-16 / 9 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (Real.rpow_nonneg hlog.le _) _)
    _ = (Real.log x ^ (M + 6)) ^ (-1 : ℝ) := by
      rw [← Real.rpow_mul hlog.le, ← Real.rpow_add hlog, ← Real.rpow_mul hlog.le]
      congr 1
      ring

/-- P0064, page 36, final display after inequality 33. Substitute tau equal to n times xi to power minus five thirds. -/
theorem lemma15_scale_identity (n xi : ℝ) (hxi : 0 < xi) :
    xi^4 * (n * xi ^ (-5 / 3 : ℝ))^3 = n^3 * xi ^ (-1 : ℝ) := by
  have hp : (xi ^ (-5 / 3 : ℝ))^3 = xi ^ (-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxi.le]
    congr 1
    norm_num
  rw [mul_pow, hp]
  calc
    xi^4 * (n^3 * xi ^ (-5 : ℝ)) = n^3 * (xi^4 * xi ^ (-5 : ℝ)) := by ring
    _ = n^3 * xi ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast xi 4, ← Real.rpow_add hxi]
      norm_num

end LeanLab.Tchudakov1938.Decomp362j
