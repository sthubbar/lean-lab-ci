import LeanLab.ChenDoubleSieve.Decomp275h

/-!
Elementary logarithmic forms of four coefficients in Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39, equations 10.2, 10.3 and 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Task275
open Wu04Functional (IsLinearSieve)

/-- The actual F0 coefficient becomes an elementary nested integral.
CONDITIONAL ON IsLinearSieve. -/
theorem F0_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 0 = 8 *
      (log 3 + ∫ t in (4 : ℝ)..6,
        (1 + ∫ x in (2 : ℝ)..((t - 1) - 1), log (x - 1) / x) / (t - 1)) := by
  change 2 * f (1 / (2 * kappa1)) / (kappa1 * exp eulerMascheroniConstant) = _
  rw [show (1 / (2 * kappa1) : ℝ) = 6 by norm_num [kappa1], linear_lower_six h]
  have hc (A : ℝ) :
      2 * ((2 * exp eulerMascheroniConstant) * A / 6) /
        (kappa1 * exp eulerMascheroniConstant) = 8 * A := by
    dsimp only [kappa1]
    field_simp [Real.exp_ne_zero]
    ring
  exact hc _

/-- The actual F1 coefficient becomes an elementary logarithmic integral.
CONDITIONAL ON IsLinearSieve. -/
theorem F1_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 1 = 8 *
      ∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1),
        (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / t := by
  have he : (∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F t) =
      (2 * exp eulerMascheroniConstant) *
        ∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1),
          (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num [kappa1, kappa2] :
      (1 / (2 * kappa2) - 1 : ℝ) ≤ 1 / (2 * kappa1) - 1)] at ht
    have hr : t ∈ Icc (3 : ℝ) 5 := by
      norm_num [kappa1, kappa2] at ht
      exact ⟨by linarith [ht.1], ht.2⟩
    simpa only [mul_div_assoc] using linear_upper_five h hr
  change 4 / exp eulerMascheroniConstant *
    (∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F t) = _
  rw [he]
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- The actual F4 coefficient contains only a double integral of elementary logarithms.
CONDITIONAL ON IsLinearSieve. -/
theorem F4_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 4 = 48 * ∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, log ((1 / 2 - t - u) / kappa1 - 1) /
        (((1 / 2 - t - u) / kappa1) * u)) / t := by
  have he : (∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t) =
      (2 * exp eulerMascheroniConstant) * ∫ t in kappa1..kappa2,
        (∫ u in t..kappa2, log ((1 / 2 - t - u) / kappa1 - 1) /
          (((1 / 2 - t - u) / kappa1) * u)) / t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)] at ht
    have hi : (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) =
        (2 * exp eulerMascheroniConstant) *
          ∫ u in t..kappa2, log ((1 / 2 - t - u) / kappa1 - 1) /
            (((1 / 2 - t - u) / kappa1) * u) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.2] at hu
      dsimp only
      rw [linear_lower_four h (F4_argument_range t u ht hu)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    dsimp only
    rw [hi]
    ring
  change 2 / (kappa1 * exp eulerMascheroniConstant) *
    (∫ t in kappa1..kappa2, (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t) = _
  rw [he]
  have hc : 2 / (kappa1 * exp eulerMascheroniConstant) *
      (2 * exp eulerMascheroniConstant) = 48 := by
    dsimp only [kappa1]
    field_simp [Real.exp_ne_zero]
    ring
  rw [← mul_assoc, hc]

/-- The actual F5 coefficient has the analogous elementary logarithmic form.
CONDITIONAL ON IsLinearSieve. -/
theorem F5_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 5 = 48 * ∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
        log ((1 / 2 - t - u) / kappa1 - 1) /
          (((1 / 2 - t - u) / kappa1) * u)) / t := by
  have he : (∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t) =
      (2 * exp eulerMascheroniConstant) * ∫ t in kappa1..kappa2,
        (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
          log ((1 / 2 - t - u) / kappa1 - 1) /
            (((1 / 2 - t - u) / kappa1) * u)) / t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)] at ht
    have hupper : kappa2 ≤ 1 / 2 - 2 * kappa1 - t := by
      norm_num [kappa1, kappa2] at *
      linarith [ht.2]
    have hi : (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) =
        (2 * exp eulerMascheroniConstant) *
          ∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
            log ((1 / 2 - t - u) / kappa1 - 1) /
              (((1 / 2 - t - u) / kappa1) * u) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hupper] at hu
      dsimp only
      rw [linear_lower_four h (F5_argument_range t u ht hu)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    dsimp only
    rw [hi]
    ring
  change 2 / (kappa1 * exp eulerMascheroniConstant) *
    (∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t) = _
  rw [he]
  have hc : 2 / (kappa1 * exp eulerMascheroniConstant) *
      (2 * exp eulerMascheroniConstant) = 48 := by
    dsimp only [kappa1]
    field_simp [Real.exp_ne_zero]
    ring
  rw [← mul_assoc, hc]

end LeanLab.ChenDoubleSieve.Task275
