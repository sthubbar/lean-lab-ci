import LeanLab.HelfgottMajor.LogMoment431
import LeanLab.HelfgottMajor.Fourier431
import LeanLab.HelfgottMajor.MellinDerivative431
import LeanLab.HelfgottMajor.Decomp389b

/-!
The differentiated Plancherel estimate on book Part IV page 434.
The scalar log squared Gaussian moment from P0014 display 4.42 is proved in LogMoment431.
The original sealed derivative energy leaf is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431c
open Real MeasureTheory Set Decomp269a Decomp389b MellinDerivative431
open scoped FourierTransform

/-- LEAF. P0014 page 43 display 4.42, the symbolic log squared Gaussian integral.
This is only a scalar moment identity, with no shift or Mellin transform.
-/
theorem gaussian_log_square_integral :
    (∫ t in Ioi (0 : ℝ), exp (-t ^ 2) * log t ^ 2) = Sec45.nLog := by
  exact LogMoment431.gaussian_log_square_integral

/-- The full critical line squared Mellin derivative is integrable.
Source book page 434, differentiated Plancherel display.
-/
theorem gaussian_derivative_line_integrable (δ : ℝ) :
    Integrable (fun t : ℝ => ‖deriv (gaussianMellin δ)
      ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hf := Fourier431.fourier_memLp_two
    (logWeightedGaussian_integrable δ) (logWeightedGaussian_memLp_two δ)
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hc := hi.comp_div (by positivity : (2 * π : ℝ) ≠ 0)
  simpa only [derivative_eq_fourier] using hc

/-- Integral Plancherel evaluates the derivative energy in terms of the actual scalar moment.
Source book page 434. The closed form nLog is not used.
-/
theorem gaussian_derivative_line_integral (δ : ℝ) :
    (∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) =
      2 * π * ∫ t in Ioi (0 : ℝ), exp (-t ^ 2) * log t ^ 2 := by
  simp_rw [derivative_eq_fourier]
  rw [Measure.integral_comp_div (fun t : ℝ => ‖𝓕 (logWeightedGaussian δ) t‖ ^ 2),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π), smul_eq_mul,
    Fourier431.integral_norm_sq_fourier
      (logWeightedGaussian_integrable δ) (logWeightedGaussian_memLp_two δ),
    logWeightedGaussian_square_integral]

/-- The two exterior derivative energies are at most the full line energy.
Source book page 434, the inequality before differentiated Plancherel.
-/
theorem derivative_energy_sum_le_full (δ : ℝ) :
    derivativeEnergy δ 1 + derivativeEnergy δ (-1) ≤
      ∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖deriv (gaussianMellin δ)
    ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2
  have hi : Integrable f := gaussian_derivative_line_integrable δ
  have hp : derivativeEnergy δ 1 ≤ ∫ t in Ioi (0 : ℝ), f t := by
    simp only [derivativeEnergy, one_mul]
    apply setIntegral_mono_set hi.integrableOn (Filter.Eventually.of_forall fun t => sq_nonneg _)
    apply Filter.Eventually.of_forall
    intro t ht
    change 1 < t at ht
    change 0 < t
    linarith
  have hn : derivativeEnergy δ (-1) ≤ ∫ t in Iic (0 : ℝ), f t := by
    simp only [derivativeEnergy, neg_one_mul]
    rw [integral_comp_neg_Ioi 1 f]
    apply setIntegral_mono_set hi.integrableOn (Filter.Eventually.of_forall fun t => sq_nonneg _)
    apply Filter.Eventually.of_forall
    intro t ht
    change t ≤ -1 at ht
    change t ≤ 0
    linarith
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hi.integrableOn hi.integrableOn
  linarith

/-- The derivative energy bound follows from the scalar log squared moment budget.
CONDITIONAL ON the explicit scalar integral bound. Book page 434 and P0014 display 4.42.
-/
theorem derivative_energy_bound_of_log_moment (δ : ℝ)
    (hlog : (∫ t in Ioi (0 : ℝ), exp (-t ^ 2) * log t ^ 2) ≤ Sec45.nLog) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  have hN := Sec45.nLog_nonneg
  have hp : 0 ≤ derivativeEnergy δ 1 := by unfold derivativeEnergy; positivity
  have hn : 0 ≤ derivativeEnergy δ (-1) := by unfold derivativeEnergy; positivity
  have hcs : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      sqrt (derivativeEnergy δ 1 + derivativeEnergy δ (-1)) * sqrt 2 := by
    have hh := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i : Fin 2 => if i = 0 then derivativeEnergy δ 1 else derivativeEnergy δ (-1))
      (g := fun _ : Fin 2 => (1 : ℝ))
      (fun i => by split <;> assumption) (fun _ => by norm_num)
    simpa [Fin.sum_univ_two] using hh
  have hb : derivativeEnergy δ 1 + derivativeEnergy δ (-1) ≤ 2 * π * Sec45.nLog := by
    calc
      _ ≤ _ := derivative_energy_sum_le_full δ
      _ = _ := gaussian_derivative_line_integral δ
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    _ ≤ sqrt (2 * π * Sec45.nLog) * sqrt 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hb) (sqrt_nonneg 2))
    _ = _ := by
      rw [← sqrt_mul (by positivity),
        show 2 * π * Sec45.nLog * 2 = 4 * (π * Sec45.nLog) by ring,
        sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_mul pi_pos.le]
      norm_num <;> ring

/-- Exactly Decomp389b.gaussian_derivative_energy_bound.
Book page 434. The scalar log squared integral has an independent clean proof.
-/
theorem gaussian_derivative_energy_bound (δ : ℝ) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  exact derivative_energy_bound_of_log_moment δ gaussian_log_square_integral.le

end LeanLab.HelfgottMajor.Decomp431c
