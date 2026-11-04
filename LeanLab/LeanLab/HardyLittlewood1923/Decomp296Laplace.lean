import LeanLab.HardyLittlewood1923.ComplexGammaIdentity
import LeanLab.HardyLittlewood1923.Decomp296Integral
import Mathlib.Analysis.Fourier.Inversion

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 25 equation 3.152.
Fourier inversion evaluates the model vertical integral.
Binary Goldbach is OPEN.
-/

open Complex Real Set MeasureTheory

namespace LeanLab.HardyLittlewood1923.Decomp296Laplace

open LeanLab.HardyLittlewood1923.Task52
open LeanLab.HardyLittlewood1923.Decomp296Integral

/-- P0004 page 25 equation 3.152, the cubic Laplace transform used for inversion. -/
theorem laplace_cube {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ 2 * Complex.exp (-z * t)) =
      2 * z ^ (-3 : ℤ) := by
  have h := gammaLaplace_eq (s := (3 : ℂ)) (by norm_num) hz
  norm_num [gammaLaplace, Complex.Gamma_nat_eq_factorial, Complex.cpow_ofNat,
    Complex.cpow_neg] at h
  convert h using 1 <;> simp <;> ring

#print axioms laplace_cube

/-- P0004 page 25 equation 3.152, the positive half line density for Fourier inversion. -/
noncomputable def cubeDensity (a t : ℝ) : ℂ :=
  ((max t 0 : ℝ) : ℂ) ^ 2 * Complex.exp (-(a : ℂ) * t)

/-- P0004 page 25 equation 3.152, convergence and continuity of the inverse density. -/
theorem cubeDensity_regular {a : ℝ} (ha : 0 < a) :
    Continuous (cubeDensity a) ∧ Integrable (cubeDensity a) := by
  have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ 2 * Complex.exp (-(a : ℂ) * t)) (Ioi 0) := by
    simpa [show (3 : ℂ) - 1 = 2 by norm_num, Complex.cpow_ofNat] using
      gammaLaplace_integrable (s := (3 : ℂ)) (by norm_num)
        (z := (a : ℂ)) (by simpa using ha)
  have he : cubeDensity a = (Ioi (0 : ℝ)).indicator
      (fun t : ℝ => (t : ℂ) ^ 2 * Complex.exp (-(a : ℂ) * t)) := by
    funext t
    by_cases ht : 0 < t
    · simp [cubeDensity, ht, max_eq_left ht.le]
    · simp [cubeDensity, ht, max_eq_right (le_of_not_gt ht)]
  refine ⟨by unfold cubeDensity; fun_prop, ?_⟩
  rw [he]
  exact hi.integrable_indicator measurableSet_Ioi

#print axioms cubeDensity_regular

/-- P0004 page 25 equation 3.152, the Fourier transform of the inverse density. -/
theorem cubeDensity_fourier {a : ℝ} (ha : 0 < a) (w : ℝ) :
    FourierTransform.fourier (cubeDensity a) w =
      2 * ((a : ℂ) + 2 * π * w * I) ^ (-3 : ℤ) := by
  let z : ℂ := (a : ℂ) + 2 * π * w * I
  have hz : 0 < z.re := by simpa [z] using ha
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply']
  have he : (fun t : ℝ => Complex.exp ((↑(-2 * π * (t * w)) : ℂ) * I) • cubeDensity a t) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 2 * Complex.exp (-z * t)) := by
    funext t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      simp only [cubeDensity, max_eq_left ht.le, smul_eq_mul]
      calc _ = (t : ℂ) ^ 2 *
          (Complex.exp ((↑(-2 * π * (t * w)) : ℂ) * I) * Complex.exp (-(a : ℂ) * t)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          dsimp [z]
          push_cast
          ring
    · simp [cubeDensity, ht, max_eq_right (le_of_not_gt ht)]
  change (∫ t : ℝ, Complex.exp ((↑(-2 * π * (t * w)) : ℂ) * I) • cubeDensity a t) = _
  rw [he, integral_indicator measurableSet_Ioi, laplace_cube hz]

#print axioms cubeDensity_fourier

/-- P0004 page 25 equation 3.152, absolute convergence on the transform side. -/
theorem cubeDensity_fourier_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (FourierTransform.fourier (cubeDensity a)) := by
  have hi : Integrable (fun θ : ℝ => ((a : ℂ) - I * θ) ^ (-3 : ℤ)) := by
    simpa using weighted_cube_integrable ha 0
  have hs := (hi.comp_mul_left' (R := -2 * π) (by positivity)).const_mul (2 : ℂ)
  have he (w : ℝ) : (a : ℂ) - I * (((-2 * π) * w : ℝ) : ℂ) =
      (a : ℂ) + 2 * π * w * I := by push_cast; ring
  change Integrable (fun w : ℝ => FourierTransform.fourier (cubeDensity a) w)
  simpa only [cubeDensity_fourier ha, he] using hs

#print axioms cubeDensity_fourier_integrable

/-- P0004 page 25 equation 3.152, with the angular normalization of modelArc. -/
theorem vertical_cube_integral {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (1 / (2 * (π : ℂ))) *
      (∫ θ : ℝ, ((a : ℂ) - I * θ) ^ (-3 : ℤ) *
        Complex.exp ((x : ℂ) * ((a : ℂ) - I * θ))) = (x : ℂ) ^ 2 / 2 := by
  let F : ℝ → ℂ := fun θ => ((a : ℂ) - I * θ) ^ (-3 : ℤ) *
    Complex.exp ((x : ℂ) * ((a : ℂ) - I * θ))
  have hv := (cubeDensity_regular ha).2.fourierInv_fourier_eq
    (cubeDensity_fourier_integrable ha) ((cubeDensity_regular ha).1.continuousAt (x := x))
  have hv' : (∫ w : ℝ, Complex.exp ((↑(2 * π * (w * x)) : ℂ) * I) *
      (2 * ((a : ℂ) + 2 * π * w * I) ^ (-3 : ℤ))) = cubeDensity a x := by
    simpa [Real.fourierInv_eq', RCLike.inner_apply', cubeDensity_fourier ha,
      smul_eq_mul, mul_comm] using hv
  have he (w : ℝ) : F ((-2 * π) * w) =
      (Complex.exp ((a : ℂ) * x) / 2) *
        (Complex.exp ((↑(2 * π * (w * x)) : ℂ) * I) *
          (2 * ((a : ℂ) + 2 * π * w * I) ^ (-3 : ℤ))) := by
    have hY : (a : ℂ) - I * (((-2 * π) * w : ℝ) : ℂ) =
        (a : ℂ) + 2 * π * w * I := by push_cast; ring
    dsimp [F]
    rw [hY, show (x : ℂ) * ((a : ℂ) + 2 * π * w * I) =
      (a : ℂ) * x + (↑(2 * π * (w * x)) : ℂ) * I by push_cast; ring, Complex.exp_add]
    ring
  have hl : (∫ w : ℝ, F ((-2 * π) * w)) = (x : ℂ) ^ 2 / 2 := by
    simp_rw [he]
    rw [integral_const_mul, hv']
    simp only [cubeDensity, max_eq_left hx.le]
    rw [neg_mul, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
  have hs := Measure.integral_comp_mul_left F (-2 * π)
  have hc : |(-2 * π : ℝ)⁻¹| = 1 / (2 * π) := by
    rw [abs_inv, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    simp [one_div]
  rw [hc, Complex.real_smul] at hs
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using hs.symm.trans hl

#print axioms vertical_cube_integral

end LeanLab.HardyLittlewood1923.Decomp296Laplace
