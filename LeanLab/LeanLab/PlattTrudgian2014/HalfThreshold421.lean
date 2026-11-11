/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 185 Corollary 1 and P0024 pages 3 and 6, existing repaired normalization.
-/
import LeanLab.PlattTrudgian2014.HalfBridge421
import LeanLab.PlattTrudgian2014.LambdaPositive

namespace LeanLab.PlattTrudgian2014

/-- P0026 page 185 Corollary 1, the exact constant also satisfies the strict measure criterion. -/
theorem pr_half_lambda_proved421 : LambdaOK (1 / 2) 0.7163435444776661 :=
  lambdaOK_of_powerLogBound (by norm_num : 1 ≤ 100) pr_half_input_proved421

/-- P0024 page 3 positive infimum, bounded by the exact P0026 Corollary 1 constant. -/
theorem lambdaPositiveThreshold_half_proved421 :
    lambdaPositiveThreshold (1 / 2) ≤ 0.7163435444776661 := by
  rw [lambdaPositiveThreshold_eq]
  exact lambdaThreshold_le (by norm_num) pr_half_lambda_proved421

/-- P0024 page 6 printed half exponent lambda bound for the positive infimum. -/
theorem lambdaPositiveThreshold_GRH_proved421 :
    lambdaPositiveThreshold (1 / 2) ≤ 0.7163436 :=
  lambdaPositiveThreshold_half_proved421.trans pr_half_constant_lt_pt.le

set_option format.width 240
#print axioms pr_half_lambda_proved421
#print axioms lambdaPositiveThreshold_half_proved421
#print axioms lambdaPositiveThreshold_GRH_proved421

end LeanLab.PlattTrudgian2014
