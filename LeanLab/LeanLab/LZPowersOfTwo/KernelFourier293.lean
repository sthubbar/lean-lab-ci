/-
P0079 page 4, display 11, proved by box convolution and Fourier inversion.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.FourierBox293
open Real Finset MeasureTheory Filter FourierTransform
open scoped Convolution
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, display 11. The full-line transform of the continuous
squared-sine kernel is the tent function. -/
theorem kernel_transform293 (η t : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, character293 (t * α) * (kernel293 η α : ℂ)) =
      ((max 0 (η - |t|) : ℝ) : ℂ) := by
  let A : Set ℝ := Set.Icc (-(η / 2)) (η / 2)
  let f : ℝ → ℂ := A.indicator (fun _ => 1)
  have hf : Integrable f := by
    dsimp [f]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hft : ∀ ξ : ℝ, 𝓕 f ξ = ((η * sinc (Real.pi * η * ξ) : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_eq']
    have heq : (fun u : ℝ => Complex.exp ((-2 * Real.pi * inner ℝ u ξ : ℝ) * Complex.I) • f u) =
        A.indicator (fun u => character293 (u * (-ξ))) := by
      funext u
      by_cases hu : u ∈ A
      · simp only [f, Set.indicator_of_mem hu, smul_eq_mul, mul_one]
        unfold character293
        rw [Real.inner_apply]
        rw [show -2 * Real.pi * (u * ξ) = 2 * Real.pi * (u * (-ξ)) by ring]
      · simp [f, hu]
    rw [heq, integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -(η / 2) ≤ η / 2 by linarith)]
    rw [character_interval293]
    rw [show Real.pi * η * (-ξ) = -(Real.pi * η * ξ) by ring, sinc_neg]
  let g : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hg : ∀ x : ℝ, g x = ((max 0 (η - |x|) : ℝ) : ℂ) := by
    intro x
    rw [show g x = ∫ u : ℝ, f u * f (x - u) by rfl]
    have heq : (fun u : ℝ => f u * f (x - u)) =
        (fun u : ℝ => ((A.indicator (fun _ => (1 : ℝ)) u *
          A.indicator (fun _ => (1 : ℝ)) (x - u) : ℝ) : ℂ)) := by
      funext u
      by_cases hu : u ∈ A <;> by_cases hv : x - u ∈ A <;> simp [f, hu, hv]
    rw [heq, integral_complex_ofReal]
    exact congrArg (fun r : ℝ => (r : ℂ)) (box_overlap293 η x)
  have hgc : Continuous g := by
    have H : g = (fun x : ℝ => ((max 0 (η - |x|) : ℝ) : ℂ)) := funext hg
    rw [H]
    fun_prop
  have hgi : Integrable g := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hfg : 𝓕 g = (fun ξ : ℝ => (kernel293 η ξ : ℂ)) := by
    funext ξ
    rw [show 𝓕 g ξ = 𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ by rfl,
      Real.fourier_mul_convolution_eq hf hf, hft]
    simp only [kernel293, pow_two, Complex.ofReal_mul]
  have hki : Integrable (𝓕 g) := by rw [hfg]; exact (kernel_integrable293 η).ofReal
  have H := hgc.fourierInv_fourier_eq hgi hki
  calc
    _ = 𝓕⁻ (𝓕 g) t := by
      rw [hfg, Real.fourierInv_eq']
      apply integral_congr_ae
      exact Eventually.of_forall (fun α => by
        simp only [smul_eq_mul, Real.inner_apply]
        unfold character293
        rw [show 2 * Real.pi * (t * α) = 2 * Real.pi * (α * t) by ring])
    _ = g t := congrFun H t
    _ = _ := hg t

/-- P0079 page 4, display 11 at zero. The total kernel mass is eta. -/
theorem kernel_integral293 (η : ℝ) (hη : 0 < η) : (∫ α : ℝ, kernel293 η α) = η := by
  have H := kernel_transform293 η 0 hη
  simp only [zero_mul, character293, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul, abs_zero, sub_zero, max_eq_right hη.le, integral_complex_ofReal] at H
  exact_mod_cast H

/-- P0079 page 4, displays 11 and 12. The full L1 kernel norm is eta. -/
theorem kernel_integral_norm293 (η : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, ‖kernel293 η α‖) = η := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η _)] using kernel_integral293 η hη

end LeanLab.LZPowersOfTwo
