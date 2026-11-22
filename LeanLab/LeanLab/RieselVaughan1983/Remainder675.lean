import LeanLab.RieselVaughan1983.Alternating675
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The scalar remainder estimate following the integral evaluation on page 53.
The constants are parameters with explicit inequalities.
The logarithmic integral identity and the paper's constant evaluations remain separate.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.RieselVaughan1983.Task675

/-- The page 53 remainder is bounded by A / z. The paper uses A = A3
and B = A4 with the stronger condition zero less than A4 less than A3 minus two. -/
theorem logarithmic_remainder_bound (z A B : ℝ) (hz : 1 ≤ z)
    (hA : 2 ≤ A) (hB0 : 0 ≤ B) (hBA : B ≤ A) :
    |-(∑' n : ℕ, (-1 : ℝ) ^ n *
      (2 / (z ^ (n + 1) * ((n : ℝ) + 1) ^ 2))) - B / (z + 1) +
      A * log (1 + 1 / z)| ≤ A / z := by
  have hz0 : 0 < z := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hS := alternating_reciprocal_square_bounds z hz
  have hloghi : log (1 + 1 / z) ≤ 1 / z := by
    have h := log_le_sub_one_of_pos (show 0 < 1 + 1 / z by positivity)
    linarith
  have hloglo : 1 / (z + 1) ≤ log (1 + 1 / z) := by
    have h := one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / z by positivity)
    have hid : 1 - (1 + 1 / z)⁻¹ = 1 / (z + 1) := by
      field_simp
      <;> ring
    rwa [hid] at h
  have hblo : B / (z + 1) ≤ A * log (1 + 1 / z) := by
    calc B / (z + 1) ≤ A / (z + 1) :=
        div_le_div_of_nonneg_right hBA (by positivity)
      _ = A * (1 / (z + 1)) := by ring
      _ ≤ A * log (1 + 1 / z) := mul_le_mul_of_nonneg_left hloglo hA0
  have hbhi : A * log (1 + 1 / z) ≤ A / z := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hloghi hA0
  have hB : 0 ≤ B / (z + 1) := by positivity
  have htwo : (2 : ℝ) / z ≤ A / z := div_le_div_of_nonneg_right hA hz0.le
  rw [abs_le]
  constructor <;> linarith [hS.1, hS.2]

end LeanLab.RieselVaughan1983.Task675
