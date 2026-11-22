import Mathlib
import LeanLab.HelfgottMajor.Contour472

/-!
Convergence for the logarithmic integrals after P0014 display 4.12 on page 35.
The tail primitive is reused from Contour472.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.LogIntegral680
open Real MeasureTheory

/-- The logarithmic square kernel of the page 35 numerical integral is integrable. -/
theorem integrable_log_square :
    Integrable (fun t : ℝ => log (t ^ 2 + 9 / 4) ^ 2 / (1 / 4 + t ^ 2)) := by
  let f : ℝ → ℝ := fun t => (1 / 2) * log (t ^ 2 + 9 / 4)
  have hc : Continuous f := by
    exact continuous_const.mul (Continuous.log (by fun_prop) (fun t => by positivity))
  have hn : ∀ t, 0 ≤ f t := by
    intro t
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg t]))
  have hs : ∀ t : ℝ, |t| ≤ 4 → f t ≤ 5 := by
    intro t ht
    have ht2 : t ^ 2 ≤ 16 := by nlinarith [sq_abs t, abs_nonneg t]
    have hl : log (t ^ 2 + 9 / 4) ≤ 10 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)
      nlinarith
    dsimp [f]
    linarith
  have hl : ∀ t : ℝ, 4 < |t| → f t ≤ log |t| + 4 := by
    intro t ht
    have ht2 : 16 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have ht0 : t ≠ 0 := by intro h; norm_num [h] at ht
    have heq : t ^ 2 + 9 / 4 = t ^ 2 * (1 + (9 / 4 : ℝ) / t ^ 2) := by
      field_simp [ht0]
      <;> ring
    have hfrac : (9 / 4 : ℝ) / t ^ 2 ≤ 8 := by
      rw [div_le_iff₀ (by positivity : 0 < t ^ 2)]
      nlinarith
    have hh := Real.log_le_sub_one_of_pos
      (by positivity : 0 < 1 + (9 / 4 : ℝ) / t ^ 2)
    dsimp [f]
    rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_abs]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hi := (Contour472.scalar_contour_energy f hc.aestronglyMeasurable hn hs hl).1
  apply (hi.const_mul 4).congr
  filter_upwards [] with t
  dsimp [f]
  ring

/-- The mixed logarithmic kernel of the page 35 square expansion is integrable. -/
theorem integrable_log :
    Integrable (fun t : ℝ => log (t ^ 2 + 9 / 4) / (1 / 4 + t ^ 2)) := by
  have hw : Integrable (fun t : ℝ => 1 / (1 / 4 + t ^ 2)) := by
    simpa only [one_div] using Contour472.cauchy_kernel_integral.1
  have hm := hw.add integrable_log_square
  have hc : Continuous (fun t : ℝ => log (t ^ 2 + 9 / 4) / (1 / 4 + t ^ 2)) := by
    exact Continuous.div (Continuous.log (by fun_prop) (fun t => by positivity))
      (by fun_prop) (fun t => by positivity)
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hn : 0 ≤ log (t ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  rw [Real.norm_of_nonneg (div_nonneg hn (by positivity))]
  change _ ≤ 1 / (1 / 4 + t ^ 2) + log (t ^ 2 + 9 / 4) ^ 2 / (1 / 4 + t ^ 2)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (log (t ^ 2 + 9 / 4) - 1 / 2)]

end LeanLab.HelfgottMajor.LogIntegral680
