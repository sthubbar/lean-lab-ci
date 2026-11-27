/-
P0069 page 51 display 5.17 and page 52 display 5.20.
This is a lab rate audit. It is not a new printed assertion of the paper.
The stretched error is smaller than every fixed inverse power of the logarithm.
A fixed inverse logarithm prefix bound does not give the required window rate.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.DQ520RateAudit697
open Filter Asymptotics

/-- Page 51 display 5.17 at z0: the two errors are little o of every fixed inverse log power. -/
theorem window_error_isLittleO_inverse_power (A : ℝ) :
    IsLittleO atTop
      (fun L : ℝ => Real.exp (-5 * L ^ (1 / 3 : ℝ)) + Real.exp (-4 * L ^ (1 / 3 : ℝ)))
      (fun L : ℝ => L ^ (-A)) := by
  have hu : Tendsto (fun L : ℝ => L ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h5 := (isLittleO_exp_neg_mul_rpow_atTop
    (a := 5) (by norm_num) (-3 * A)).comp_tendsto hu
  have h4 := (isLittleO_exp_neg_mul_rpow_atTop
    (a := 4) (by norm_num) (-3 * A)).comp_tendsto hu
  apply (h5.add h4).congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hL]
  congr 1
  ring

/-- Page 51 display 5.17, lab audit: no fixed inverse log power is O of its stretched error. -/
theorem inverse_power_not_isBigO_window_error (A : ℝ) :
    ¬ IsBigO atTop (fun L : ℝ => L ^ (-A))
      (fun L : ℝ => Real.exp (-5 * L ^ (1 / 3 : ℝ)) + Real.exp (-4 * L ^ (1 / 3 : ℝ))) := by
  apply (window_error_isLittleO_inverse_power A).not_isBigO
  exact (Filter.Eventually.of_forall (fun L : ℝ =>
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne')).frequently

end LeanLab.BHP1997.DQ520RateAudit697
