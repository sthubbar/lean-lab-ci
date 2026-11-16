import LeanLab.ChenDoubleSieve.I1Reduction
import LeanLab.ChenDoubleSieve.BuchstabTail

/-!
Exact limits of constant cap certificates for Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
These negative certificates concern proof methods. They do not negate an I2 leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Finset
namespace LeanLab.ChenDoubleSieve.Task587

/-- The row four D2,9 reciprocal integral is strictly larger than 2202/100000.
Wu 2004 page 26, derived exact logarithmic lower certificate. -/
theorem r3Nine_reciprocal_gt : (2202 / 100000 : ℝ) <
    Wu04I1.reciprocalIntegral (5 / 2) (89 / 25) := by
  have hr : Wu04I1.reciprocalIntegral (5 / 2) (89 / 25) =
      Wu04Reduced.reducedVolume (1 / (89 / 25)) (1 / (5 / 2)) :=
    Wu04I1.reciprocal_reduction (by norm_num) (by norm_num)
  rw [hr, Wu04Reduced.reducedVolume_parameters (by norm_num) (by norm_num)]
  have hl := (Wu04Integral.log_bounds 12 (y := (178 / 125 : ℝ)) (by norm_num)).1
  have hc : (2202 / 100000 : ℝ) <
      (303 / 50 : ℝ) * Wu04Integral.logLower 12 (178 / 125) - 53 / 25 := by
    norm_num [Wu04Integral.logLower, sum_range_succ]
  norm_num at hl ⊢
  linarith

/-- Even exact reciprocal integration with the global cap exceeds the original target.
Wu 2004 page 26, D2,9 at Table 1 row four. -/
theorem r3Nine_global_cap_too_large : (12408337 / 1000000000 : ℝ) <
    (5671433 / 10000000 : ℝ) * Wu04I1.reciprocalIntegral (5 / 2) (89 / 25) := by
  have h := mul_lt_mul_of_pos_left r3Nine_reciprocal_gt
    (by norm_num : (0 : ℝ) < 5671433 / 10000000)
  linarith

/-- The cap after three also fails if applied to the full reciprocal integral.
Wu 2004 page 26, D2,9 at Table 1 row four. -/
theorem r3Nine_three_cap_too_large : (12408337 / 1000000000 : ℝ) <
    (566 / 1000 : ℝ) * Wu04I1.reciprocalIntegral (5 / 2) (89 / 25) := by
  have h := mul_lt_mul_of_pos_left r3Nine_reciprocal_gt
    (by norm_num : (0 : ℝ) < 566 / 1000)
  linarith

end LeanLab.ChenDoubleSieve.Task587
