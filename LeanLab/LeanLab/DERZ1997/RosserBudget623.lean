import Mathlib

/-!
A limitation of the published Rosser budget in the height-fourteen source triage.
Kadiri and Lumley 2014, page 6 display 2.32 and page 11 Theorem 3.2 part d.
This is a derived numerical comparison and makes no claim that the source is wrong.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.RosserBudget623

/-- The Rosser upper budget at height fourteen exceeds two positive zeros.
It therefore does not exclude a reflected off-line pair below that height.
Source constants are from Rosser as quoted by Kadiri and Lumley, pages 6 and 11.
-/
theorem rosser_budget_fourteen_gt_two623 :
    (2 : ℝ) <
      (14 / (2 * Real.pi) * Real.log (14 / (2 * Real.pi)) -
        14 / (2 * Real.pi) + 7 / 8) +
      0.137 * Real.log 14 + 0.443 * Real.log (Real.log 14) + 1.588 := by
  let y : ℝ := 14 / (2 * Real.pi)
  have hy : 0 < y := by dsimp [y]; positivity
  have hconvex : y - 1 ≤ y * Real.log y := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hy) hy.le
    calc
      y - 1 = y * (1 - y⁻¹) := by rw [mul_sub, mul_one, mul_inv_cancel₀ hy.ne']
      _ ≤ _ := hh
  have hexp : Real.exp 2 < 14 := by
    calc
      Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ < (3 : ℝ) ^ 2 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ < 14 := by norm_num
  have hlog : 2 < Real.log 14 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  have hloglog : Real.log 2 ≤ Real.log (Real.log 14) :=
    Real.log_le_log (by norm_num) hlog.le
  change 2 < (y * Real.log y - y + 7 / 8) +
    0.137 * Real.log 14 + 0.443 * Real.log (Real.log 14) + 1.588
  nlinarith [Real.log_two_gt_d9]

end LeanLab.DERZ1997.RosserBudget623
