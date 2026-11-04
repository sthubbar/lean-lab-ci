import LeanLab.ExceptionalSet.TriangleKernel264
import LeanLab.ExceptionalSet.State1539Data264

/-
The explicit Fourier kernel of Brudern and Perelli 1998.
Source: page 356 displays 2 and 3.
AI wrote the Lean code. Goldbach is open.
-/

open MeasureTheory FourierTransform
open LeanLab.ExceptionalSet.U1539 (Kfun)

namespace LeanLab.ExceptionalSet.KernelTransform264

/-- The trapezoid weight as a difference of two triangles. -/
noncomputable def weight (Δ y : ℝ) : ℝ :=
  1 / Δ * max 0 (1 - |y|) - (1 / Δ - 1) * max 0 (1 - |y / (1 - Δ)|)

/-- The explicit kernel is integrable when its two scales are positive. -/
theorem Kfun_integrable {Δ : ℝ} (_hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Integrable (fun x : ℝ => (Kfun Δ x : ℂ)) := by
  have hc : 1 - Δ ≠ 0 := by linarith
  have hbase := TriangleKernel264.sinc_sq_integrable
  have hscale := hbase.comp_mul_left' hc
  convert (hbase.const_mul ((1 / Δ : ℝ) : ℂ)).sub
    (hscale.const_mul ((1 / Δ * (1 - Δ) ^ 2 : ℝ) : ℂ)) using 1
  funext x
  simp only [Kfun, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    mul_assoc, Pi.sub_apply]

/-- The Fourier integral of the explicit kernel is the trapezoid weight. -/
theorem fourier_Kfun {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (y : ℝ) :
    𝓕 (fun x : ℝ => (Kfun Δ x : ℂ)) y = (weight Δ y : ℂ) := by
  let F : ℝ → ℂ := fun x => (Real.sinc (Real.pi * x) ^ 2 : ℝ)
  let G : ℝ → ℂ := fun x => (Real.sinc (Real.pi * ((1 - Δ) * x)) ^ 2 : ℝ)
  let d : ℂ := (1 / Δ : ℝ)
  let e : ℂ := (1 / Δ * (1 - Δ) ^ 2 : ℝ)
  have hc : 0 < 1 - Δ := by linarith
  have hF : Integrable F := TriangleKernel264.sinc_sq_integrable
  have hG : Integrable G := hF.comp_mul_left' hc.ne'
  have hfun : (fun x : ℝ => (Kfun Δ x : ℂ)) = fun x => d * F x - e * G x := by
    funext x
    dsimp [Kfun, d, e, F, G]
    push_cast
    simp only [mul_assoc]
  have hconst (r : ℂ) (f : ℝ → ℂ) : 𝓕 (fun x => r * f x) y = r * 𝓕 f y := by
    simp only [Real.fourier_eq]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  have hsub : 𝓕 (fun x => d * F x - e * G x) y =
      𝓕 (fun x => d * F x) y - 𝓕 (fun x => e * G x) y := by
    simp only [Real.fourier_eq, smul_sub]
    apply integral_sub
    · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ ℝ) (by fun_prop) y).2 (hF.const_mul d)
    · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ ℝ) (by fun_prop) y).2 (hG.const_mul e)
  rw [hfun, hsub, hconst, hconst]
  change d * 𝓕 (fun x : ℝ => (Real.sinc (Real.pi * x) ^ 2 : ℝ) : ℝ → ℂ) y -
    e * 𝓕 (fun x : ℝ => (Real.sinc (Real.pi * ((1 - Δ) * x)) ^ 2 : ℝ) : ℝ → ℂ) y = _
  rw [TriangleKernel264.fourier_sinc_sq, TriangleKernel264.fourier_scaled_sinc_sq hc]
  dsimp [d, e, weight]
  push_cast
  have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hcc : (1 - (Δ : ℂ)) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp [hΔc, hcc]

/-- The trapezoid vanishes outside the unit interval. -/
theorem weight_zero {Δ y : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hy : 1 ≤ |y|) :
    weight Δ y = 0 := by
  have hc : 0 < 1 - Δ := by linarith
  have hd : 1 ≤ |y / (1 - Δ)| := by
    rw [abs_div, abs_of_pos hc, le_div_iff₀ hc]
    linarith
  rw [weight, max_eq_left (by linarith : 1 - |y| ≤ 0),
    max_eq_left (by linarith : 1 - |y / (1 - Δ)| ≤ 0)]
  ring

/-- The trapezoid equals one on its central plateau. -/
theorem weight_one {Δ y : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hy : |y| ≤ 1 - Δ) :
    weight Δ y = 1 := by
  have hc : 0 < 1 - Δ := by linarith
  have hd : |y / (1 - Δ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
    simpa using hy
  rw [weight, max_eq_right (by linarith : 0 ≤ 1 - |y|),
    max_eq_right (by linarith : 0 ≤ 1 - |y / (1 - Δ)|), abs_div, abs_of_pos hc]
  field_simp
  <;> ring

/-- The outer piece is the linear ramp. -/
theorem weight_ramp {Δ y : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hy : 1 - Δ ≤ |y|) (hy1 : |y| ≤ 1) : weight Δ y = (1 - |y|) / Δ := by
  have hc : 0 < 1 - Δ := by linarith
  have hd : 1 ≤ |y / (1 - Δ)| := by
    rw [abs_div, abs_of_pos hc, le_div_iff₀ hc]
    simpa using hy
  rw [weight, max_eq_right (by linarith : 0 ≤ 1 - |y|),
    max_eq_left (by linarith : 1 - |y / (1 - Δ)| ≤ 0)]
  ring

/-- The paper's Fourier weight lies between zero and one. -/
theorem weight_bounds {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (y : ℝ) :
    0 ≤ weight Δ y ∧ weight Δ y ≤ 1 := by
  by_cases hsmall : |y| ≤ 1 - Δ
  · rw [weight_one hΔ hΔ1 hsmall]
    norm_num
  · by_cases hlarge : 1 ≤ |y|
    · rw [weight_zero hΔ hΔ1 hlarge]
      norm_num
    · rw [weight_ramp hΔ hΔ1 (le_of_not_ge hsmall) (le_of_not_ge hlarge)]
      constructor
      · exact div_nonneg (by linarith) hΔ.le
      · apply (div_le_one hΔ).mpr
        linarith

/-- The paper's explicit kernel is continuous. -/
theorem Kfun_continuous (Δ : ℝ) : Continuous (fun x : ℝ => (Kfun Δ x : ℂ)) := by
  unfold Kfun
  fun_prop

/-- The paper's Fourier convention gives the same trapezoid. -/
theorem ftR_Kfun {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (y : ℝ) :
    U1539.ftR (fun x : ℝ => (Kfun Δ x : ℂ)) y = (weight Δ y : ℂ) := by
  have he : U1539.ftR (fun x : ℝ => (Kfun Δ x : ℂ)) y =
      𝓕 (fun x : ℝ => (Kfun Δ x : ℂ)) y := by
    simp only [U1539.ftR, U1539.eC, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards with x
    have hx : 2 * (Real.pi : ℂ) * Complex.I * (-(y * x) : ℝ) =
        ↑(-2 * Real.pi * x * y) * Complex.I := by push_cast; ring
    rw [hx]
    ring
  rw [he, fourier_Kfun hΔ hΔ1]

/-- The Fourier transform of the paper kernel is zero at absolute frequency at least one. -/
theorem ftR_Kfun_zero {Δ y : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hy : 1 ≤ |y|) :
    U1539.ftR (fun x : ℝ => (Kfun Δ x : ℂ)) y = 0 := by
  rw [ftR_Kfun hΔ hΔ1, weight_zero hΔ hΔ1 hy, Complex.ofReal_zero]

end LeanLab.ExceptionalSet.KernelTransform264
