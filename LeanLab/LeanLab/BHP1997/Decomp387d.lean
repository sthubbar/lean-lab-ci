/-
BHP1997, pages 3, 52 and 53. Elementary logarithmic rescaling for an upper weight.
This does not assert a distribution or mean square estimate for a rescaled family.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165

namespace LeanLab.BHP1997.Task387
open Classical

/-- Pages 52 and 53, auxiliary normalization factor. It is log m divided
by log Y on the nontrivial dyadic range, and one elsewhere. -/
noncomputable def upperLogFactor (Y : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ Y ∧ Y ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*Y then Real.log m/Real.log Y else 1

/-- Pages 52 and 53, auxiliary normalization. The logarithmic upper
rescaling factor always lies between one and two. -/
theorem upper_log_factor_bounds (Y : ℝ) (m : ℕ) :
    1 ≤ upperLogFactor Y m ∧ upperLogFactor Y m ≤ 2 := by
  unfold upperLogFactor
  split_ifs with h
  · have hY0 : 0 < Y := by linarith [h.1]
    have hY1 : 1 < Y := by linarith [h.1]
    have hm0 : (0 : ℝ) < m := hY0.trans_le h.2.1
    have hlog : 0 < Real.log Y := Real.log_pos hY1
    have hlo := Real.log_le_log hY0 h.2.1
    have hhi := Real.log_le_log hm0 h.2.2
    rw [Real.log_mul (by norm_num) hY0.ne'] at hhi
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h.1
    constructor
    · exact (le_div_iff₀ hlog).mpr (by simpa using hlo)
    · exact (div_le_iff₀ hlog).mpr (by linarith)
  · norm_num

/-- Pages 3 and 53, auxiliary upper normalization. Multiplying an upper
prime majorant by this factor preserves its pointwise prime majorant. -/
theorem upper_log_rescaling_majorant {Y a ρ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (ha : ρ ≤ a) :
    ρ ≤ upperLogFactor Y m*a := by
  have hfac := upper_log_factor_bounds Y m
  calc
    ρ ≤ a := ha
    _ = 1*a := by ring
    _ ≤ upperLogFactor Y m*a := mul_le_mul_of_nonneg_right hfac.1 (hρ.trans ha)

/-- Page 3 condition ii and page 52 normalization. Rescaling a divisor
bounded coefficient family costs at most a factor two in its bound.
No distribution estimate is inferred from this pointwise statement. -/
theorem upper_log_rescaling_divisor_bound {B C : ℝ}
    {a : ℝ → ℕ → ℝ} (Y : ℝ → ℝ)
    (ha : ∀ x k, |a x k| ≤ C*((k.divisors.card : ℕ) : ℝ)^B) :
    ∀ x k, |upperLogFactor (Y x) k*a x k| ≤
      (2*C)*((k.divisors.card : ℕ) : ℝ)^B := by
  intro x k
  have hf := upper_log_factor_bounds (Y x) k
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ upperLogFactor (Y x) k)]
  calc
    _ ≤ 2*|a x k| := mul_le_mul_of_nonneg_right hf.2 (abs_nonneg _)
    _ ≤ 2*(C*((k.divisors.card : ℕ) : ℝ)^B) := mul_le_mul_of_nonneg_left (ha x k) (by norm_num)
    _ = _ := by ring

end LeanLab.BHP1997.Task387
