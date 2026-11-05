/-
Ramaré 1995 p. 678, the small modulus numerical coefficient in Proposition 1.
The logarithmic ratio and the displayed rational calculation are elementary.
The normalized coefficient theorem keeps the actual arithmetic progression bounds explicit.
It does not prove those analytic bounds or the full Proposition 1.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Ramare1995.Budget369

/-- The p. 678 factor log X divided by log of 2X is at least 0.9897 for X at least exp 67. -/
theorem log_ratio_ge (X : ℝ) (hX : Real.exp 67 ≤ X) :
    (0.9897 : ℝ) ≤ Real.log X / Real.log (2 * X) := by
  have hX0 : 0 < X := (Real.exp_pos 67).trans_le hX
  have hL : (67 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 67) hX
    simpa only [Real.log_exp] using h
  have he : Real.log (2 * X) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  have hd : 0 < Real.log (2 * X) := by
    rw [he]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  apply (le_div_iff₀ hd).mpr
  rw [he]
  have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  nlinarith

/-- The literal rational lower bound in the small modulus display on p. 678. -/
theorem small_modulus_scalar :
    (0.4921 : ℝ) ≤ ((0.66025 - 0.00369) / 1.320323) * 0.9897 := by
  norm_num

/-- The small modulus coefficient follows from the printed normalized factor bounds.
CONDITIONAL ON the displayed upper bound for C and lower bound for u.
Instantiating u by the actual progression sum still requires the paper analytic estimates. -/
theorem normalized_main_budget (X C u : ℝ) (hX : Real.exp 67 ≤ X)
    (hC0 : 0 < C) (hC : C ≤ 1.320323) (hu : 0.66025 - 0.00369 ≤ u) :
    (0.4921 : ℝ) ≤ (u / C) * (Real.log X / Real.log (2 * X)) := by
  let v : ℝ := (0.66025 - 0.00369) / 1.320323
  have hv : 0 ≤ v := by norm_num [v]
  have hvc : v * C ≤ u := by
    calc
      v * C ≤ v * 1.320323 := mul_le_mul_of_nonneg_left hC hv
      _ = 0.66025 - 0.00369 := by norm_num [v]
      _ ≤ u := hu
  have hquot : v ≤ u / C := (le_div_iff₀ hC0).mpr hvc
  have hq0 : 0 ≤ u / C := div_nonneg (by linarith) hC0.le
  have hm := mul_le_mul hquot (log_ratio_ge X hX) (by norm_num : (0 : ℝ) ≤ 0.9897) hq0
  exact small_modulus_scalar.trans hm

end LeanLab.Ramare1995.Budget369
