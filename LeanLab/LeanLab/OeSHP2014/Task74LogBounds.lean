import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Rational logarithm bounds for the Table 12 checks.
The estimates use the proved Taylor remainder in Mathlib.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- An elementary enclosure of the logarithm used on pages 2056 and 2057. -/
theorem log10_bounds :
    (2302585092994 / 10^12 : ℝ) ≤ Real.log 10 ∧
      Real.log 10 ≤ (2302585092995 / 10^12 : ℝ) := by
  have l2 := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num)
    (by norm_num) 14
  have u2 := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ)) (by norm_num)
    (by norm_num) 14
  have lq := Real.sum_range_le_log_div (x := (1 / 9 : ℝ)) (by norm_num)
    (by norm_num) 7
  have uq := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ)) (by norm_num)
    (by norm_num) 7
  norm_num [Finset.sum_range_succ] at l2 u2 lq uq
  have he : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  constructor <;> rw [he] <;> linarith

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.log10_bounds
