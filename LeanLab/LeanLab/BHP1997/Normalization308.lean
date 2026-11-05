/-
BHP1997, page 52. Elementary steps behind displays 5.19 and 5.22.
The actual moment and Perron estimates remain analytic inputs.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Task308
open MeasureTheory Set Complex

/-- Page 52 before display 5.19. The weighted kernel normalized by T squared
increases with positive T. This is the paper's smaller T2 argument. -/
theorem normalized_kernel_mono {s T a : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    (ha : 0 ≤ a) (t : ℝ) :
    a * s^2 / (s^2+t^2) ≤ a * T^2 / (T^2+t^2) := by
  have hT : 0 < T := hs.trans_le hsT
  have hds : 0 < s^2+t^2 := by positivity
  have hdT : 0 < T^2+t^2 := by positivity
  have hsq : s^2 ≤ T^2 := pow_le_pow_left₀ hs.le hsT 2
  apply (div_le_div_iff₀ hds hdT).2
  nlinarith only [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hsq)) (sq_nonneg t)]

/-- Page 52 before display 5.19. Finite weighted moments normalized by T squared
increase with positive T. Continuity makes every displayed integral genuine. -/
theorem normalized_weighted_moment_mono {α : Type*} (E : Finset α)
    (f : α → ℝ → ℝ) {a b s T : ℝ} (hab : a ≤ b) (hs : 0 < s) (hsT : s ≤ T)
    (hc : ∀ χ ∈ E, ContinuousOn (f χ) (Icc a b))
    (hf : ∀ χ ∈ E, ∀ t ∈ Icc a b, 0 ≤ f χ t) :
    s^2 * (∑ χ ∈ E, ∫ t in a..b, f χ t / (s^2+t^2)) ≤
      T^2 * (∑ χ ∈ E, ∫ t in a..b, f χ t / (T^2+t^2)) := by
  have hi (u : ℝ) (hu : 0 < u) (χ : α) (hχ : χ ∈ E) :
      IntervalIntegrable (fun t => f χ t * u^2 / (u^2+t^2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ((hc χ hχ).mul continuousOn_const).div
      (continuousOn_const.add (continuousOn_id.pow 2))
    intro t ht
    exact ne_of_gt (by positivity : 0 < u^2+t^2)
  have hh := Finset.sum_le_sum (fun χ hχ =>
    intervalIntegral.integral_mono_on hab (hi s hs χ hχ) (hi T (hs.trans_le hsT) χ hχ)
      (fun t ht => normalized_kernel_mono hs hsT (hf χ hχ t ht) t))
  have heq (u : ℝ) :
      (∑ χ ∈ E, ∫ t in a..b, f χ t * u^2 / (u^2+t^2)) =
        u^2 * (∑ χ ∈ E, ∫ t in a..b, f χ t / (u^2+t^2)) := by
    simp_rw [show ∀ χ t, f χ t * u^2 / (u^2+t^2) =
      u^2 * (f χ t / (u^2+t^2)) by intros; ring]
    simp only [intervalIntegral.integral_const_mul, Finset.mul_sum]
  rw [heq, heq] at hh
  exact hh

/-- Page 52 before display 5.19. A moment bound proportional to T to negative two
remains valid when T is replaced by a smaller positive value.
CONDITIONAL on the actual larger-scale moment estimate. -/
theorem weighted_moment_shrink {α : Type*} (E : Finset α)
    (f : α → ℝ → ℝ) {a b s T D : ℝ} (hab : a ≤ b) (hs : 0 < s) (hsT : s ≤ T)
    (hc : ∀ χ ∈ E, ContinuousOn (f χ) (Icc a b))
    (hf : ∀ χ ∈ E, ∀ t ∈ Icc a b, 0 ≤ f χ t)
    (hbound : (∑ χ ∈ E, ∫ t in a..b, f χ t / (T^2+t^2)) ≤ D / T^2) :
    (∑ χ ∈ E, ∫ t in a..b, f χ t / (s^2+t^2)) ≤ D / s^2 := by
  have hmono := normalized_weighted_moment_mono E f hab hs hsT hc hf
  have hT : T ≠ 0 := ne_of_gt (hs.trans_le hsT)
  have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg T)
  have he : T^2 * (D / T^2) = D := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ (sq_pos_of_pos hs)).2
  nlinarith only [hmono, hh]

/-- Page 52, display 5.22. A centered squared error at scale z is z squared
times the error at scale one. The identity also holds for totalized integrals. -/
theorem centered_error_scale {α : Type*} (E : Finset α) (F : α → ℝ → ℂ)
    (z a b : ℝ) :
    (∑ χ ∈ E, ∫ y in a..b, ‖(z : ℂ) * F χ y‖^2) =
      z^2 * (∑ χ ∈ E, ∫ y in a..b, ‖F χ y‖^2) := by
  have hp (χ : α) (y : ℝ) : ‖(z : ℂ) * F χ y‖^2 = z^2 * ‖F χ y‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hp]
  simp only [intervalIntegral.integral_const_mul, Finset.mul_sum]

/-- Page 52, from the z0 error estimate to display 5.22. A nonzero reference scale
with a bound proportional to its square gives the same bound at every scale.
CONDITIONAL on the supplied reference-scale error estimate. -/
theorem centered_error_rescale {α : Type*} (E : Finset α) (F : α → ℝ → ℂ)
    {z0 R : ℝ} (hz0 : z0 ≠ 0) (z a b : ℝ)
    (hbound : (∑ χ ∈ E, ∫ y in a..b, ‖(z0 : ℂ) * F χ y‖^2) ≤ z0^2 * R) :
    (∑ χ ∈ E, ∫ y in a..b, ‖(z : ℂ) * F χ y‖^2) ≤ z^2 * R := by
  rw [centered_error_scale] at hbound ⊢
  have hh := (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hz0)).mp hbound
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg z)

end LeanLab.BHP1997.Task308
