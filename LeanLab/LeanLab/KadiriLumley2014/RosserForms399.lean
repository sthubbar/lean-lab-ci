/-
P0059 page 7 displays 2.40 to 2.42 and source 4, arXiv 1310.6374 page 9.
The exact integral forms of the three remaining Rosser coefficients.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.RosserIntegral399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory
open Task259

/-- The difference of squared endpoint logarithms equals the product printed for S1. -/
theorem log_square_difference_product {c U V : ℝ} (hc : 0 < c) (hU : 0 < U) (hV : 0 < V) :
    ((Real.log (V / c)) ^ 2 - (Real.log (U / c)) ^ 2) / 2 =
      Real.log (V / U) * Real.log (Real.sqrt (V * U) / c) := by
  have hs : 0 < Real.sqrt (V * U) := Real.sqrt_pos.mpr (mul_pos hV hU)
  rw [Real.log_div hV.ne' hc.ne', Real.log_div hU.ne' hc.ne',
    Real.log_div hV.ne' hU.ne', Real.log_div hs.ne' hc.ne',
    Real.log_sqrt (mul_nonneg hV.le hU.le), Real.log_mul hV.ne' hU.ne']
  ring

/-- The first integral on cited page 9 has the exact square-root product spelling used by S1. -/
theorem integral_log_reciprocal_product {c U V : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hUV : U ≤ V) :
    (∫ t in U..V, Real.log (t / c) / t) =
      Real.log (V / U) * Real.log (Real.sqrt (V * U) / c) := by
  rw [integral_log_reciprocal hc hU hUV,
    log_square_difference_product hc hU (hU.trans_le hUV)]

/-- S1 is its exact logarithmic integral times the Rosser coefficient, plus the lower boundary error. -/
theorem zeroS1_integral {T1 : ℝ} (hT0 : 1132491 ≤ T1) :
    zeroS1 T1 = (1 / (2 * π) + countQ 1132491) *
      (∫ t in (1132491 : ℝ)..T1, Real.log (t / (2 * π)) / t) +
        2 * countRemainder 1132491 / 1132491 := by
  rw [integral_log_reciprocal_product (by positivity) (by norm_num) hT0]
  unfold zeroS1
  ring

/-- S2 is its exact finite logarithmic power integral times the Rosser coefficient, plus the lower boundary error. -/
theorem zeroS2_integral {m : ℕ} (hm : 0 < m) {T1 : ℝ}
    (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000) :
    zeroS2 m T1 = (1 / (2 * π) + countQ T1) *
      (∫ t in T1..(30610000000 : ℝ), Real.log (t / (2 * π)) / t ^ (m + 1)) +
        2 * countRemainder T1 / T1 ^ (m + 1) := by
  rw [integral_log_power hm (by positivity) (by linarith) hTH]
  rfl

/-- S3 is its exact infinite logarithmic power integral times the Rosser coefficient, plus the boundary error at H. -/
theorem zeroS3_integral {m : ℕ} (hm : 0 < m) :
    zeroS3 m = (1 / (2 * π) + countQ 30610000000) *
      (∫ t in Ioi (30610000000 : ℝ), Real.log (t / (2 * π)) / t ^ (m + 1)) +
        2 * countRemainder 30610000000 / (30610000000 : ℝ) ^ (m + 1) := by
  rw [integral_Ioi_log_power hm (by positivity) (by norm_num)
    (by linarith [Real.pi_lt_four])]
  rfl

end LeanLab.KadiriLumley2014.Task399
