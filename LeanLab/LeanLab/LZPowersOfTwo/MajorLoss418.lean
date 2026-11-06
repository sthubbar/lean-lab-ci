/-
Negative route checks for the remaining P0079 replacement input.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, displays 33 to 35, a lab check of the pointwise alternative.
The naive major-arc scale X to the four-thirds grows without bound relative to X.
This is a proof-method loss, not a claim of a paper error. -/
theorem major_pointwise_loss418 :
    Tendsto (fun X : ℝ => X ^ (4 / 3 : ℝ) / X) atTop atTop := by
  have H := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [← Real.rpow_sub_one hX.ne']
  norm_num

/-- P0079 page 2, the ordered coefficient hypothesis, a lab bridge check.
For a strictly ordered opposite-sign pair, swapping and negating violates
the sealed lower bound of one on the absolute coefficient ratio. -/
theorem reversed_ratio_lt418 (l1 l2 : ℝ) (h1 : 0 < l1) (h2 : l2 < 0)
    (hr : 1 < |l1 / l2|) : |(-l2) / (-l1)| < 1 := by
  rw [neg_div_neg_eq, abs_div]
  apply (div_lt_one (abs_pos.mpr h1.ne')).mpr
  rw [abs_div] at hr
  exact (one_lt_div (abs_pos.mpr h2.ne)).mp hr

end LeanLab.LZPowersOfTwo
