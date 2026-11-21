/-
P0069 page 52, the step from 5.1 and 5.2 to a smaller positive T2 before display 5.19.
This is the scalar kernel comparison. The Perron mean square argument remains separate.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.DQ520ScaleTransfer
open MeasureTheory

/-- Page 52, multiplying the weighted kernel by T2 squared makes it monotone in T2. -/
theorem scaled_kernel_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    a ^ 2 / (a ^ 2 + t ^ 2) ≤ b ^ 2 / (b ^ 2 + t ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  have ha2 : 0 < a ^ 2 + t ^ 2 := by positivity
  have hb2 : 0 < b ^ 2 + t ^ 2 := by positivity
  rw [div_le_div_iff₀ ha2 hb2]
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg t)]

/-- Page 52, the pointwise comparison used for each nonnegative mean square integrand. -/
theorem weighted_kernel_mono {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hv : 0 ≤ v) (t : ℝ) :
    a ^ 2 * (v / (a ^ 2 + t ^ 2)) ≤ b ^ 2 * (v / (b ^ 2 + t ^ 2)) := by
  calc
    _ = (a ^ 2 / (a ^ 2 + t ^ 2)) * v := by ring
    _ ≤ (b ^ 2 / (b ^ 2 + t ^ 2)) * v :=
      mul_le_mul_of_nonneg_right (scaled_kernel_mono ha hab t) hv
    _ = _ := by ring

/-- Page 52, a bound C divided by T2 squared transfers to every smaller positive T2. -/
theorem weighted_integral_smaller_scale {a b u v K : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (huv : u ≤ v) (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hia : IntervalIntegrable (fun t => f t / (a ^ 2 + t ^ 2)) volume u v)
    (hib : IntervalIntegrable (fun t => f t / (b ^ 2 + t ^ 2)) volume u v)
    (hbound : (∫ t in u..v, f t / (b ^ 2 + t ^ 2)) ≤ K / b ^ 2) :
    (∫ t in u..v, f t / (a ^ 2 + t ^ 2)) ≤ K / a ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on huv (hia.const_mul (a ^ 2))
    (hib.const_mul (b ^ 2)) (fun t _ => weighted_kernel_mono ha hab (hf t) t)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hlarge : b ^ 2 * (∫ t in u..v, f t / (b ^ 2 + t ^ 2)) ≤ K := by
    calc _ ≤ b ^ 2 * (K / b ^ 2) := mul_le_mul_of_nonneg_left hbound (sq_nonneg b)
      _ = K := by field_simp
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith

end LeanLab.BHP1997.DQ520ScaleTransfer
