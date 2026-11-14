/-
Harmonicity of the normalized strip kernel in Rademacher page 193 display 2.51.
This does not interchange derivatives with the logarithmic boundary integral.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp560d

namespace LeanLab.BHP1997.Decomp560e
open Complex Set Filter InnerProductSpace
open scoped Topology
open LeanLab.BHP1997.Decomp560d

/-- An analytic complex kernel whose imaginary part is Rademacher's strip Poisson kernel. -/
noncomputable def stripCauchyKernel (z : ℂ) : ℂ :=
  (1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z))⁻¹

/-- The complex strip kernel is analytic in the open strip from zero to one.
Auxiliary analytic representation of Rademacher page 193 display 2.51. -/
theorem stripCauchyKernel_analyticAt {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    AnalyticAt ℂ stripCauchyKernel z := by
  have hi : 0 < (Complex.exp ((Real.pi : ℂ) * Complex.I * z)).im := by
    rw [Complex.exp_im]
    apply mul_pos (Real.exp_pos _)
    have hh : (((Real.pi : ℂ) * Complex.I) * z).im = Real.pi * z.re := by simp
    rw [hh]
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hz0) (by nlinarith [Real.pi_pos])
  have hn : 1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.zero_im] at hh
    linarith
  exact (show AnalyticAt ℂ (fun z : ℂ => 1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z)) z by
    fun_prop).inv hn

/-- The imaginary part of the analytic kernel is exactly the real Poisson kernel.
Source Rademacher page 193 display 2.51, with an auxiliary exponential representation. -/
theorem stripCauchyKernel_im {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    (stripCauchyKernel ((σ : ℂ) + (t : ℂ) * Complex.I)).im = stripPoissonKernel σ t := by
  have hre : (((Real.pi : ℂ) * Complex.I) * ((σ : ℂ) + (t : ℂ) * Complex.I)).re = -Real.pi * t := by
    simp
  have him : (((Real.pi : ℂ) * Complex.I) * ((σ : ℂ) + (t : ℂ) * Complex.I)).im = Real.pi * σ := by
    simp
  have hsq := Real.sin_sq_add_cos_sq (Real.pi * σ)
  have hexp : Real.exp (-Real.pi * t) * Real.exp (Real.pi * t) = 1 := by
    rw [← Real.exp_add, show -Real.pi * t + Real.pi * t = 0 by ring, Real.exp_zero]
  have hnorm : (1 - Real.exp (-Real.pi * t) * Real.cos (Real.pi * σ)) ^ 2 +
      (Real.exp (-Real.pi * t) * Real.sin (Real.pi * σ)) ^ 2 =
      Real.exp (-Real.pi * t) * (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * σ))) := by
    rw [Real.cosh_eq]
    simp only [← neg_mul] at *
    nlinarith [congrArg (fun y : ℝ => Real.exp (-Real.pi * t) ^ 2 * y) hsq]
  simp only [stripCauchyKernel, Complex.inv_im, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_re, Complex.exp_im, hre, him]
  simp only [zero_sub, neg_neg, ← pow_two, neg_sq]
  rw [hnorm]
  dsimp [stripPoissonKernel]
  field_simp [Real.exp_ne_zero, (kernel_denominator_pos hσ0 hσ1 t).ne']

/-- Rademacher page 193 display 2.51, the strip Poisson kernel is harmonic in the open strip.
The complex representation avoids a separate second derivative calculation. -/
theorem stripPoissonKernel_harmonicAt {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    HarmonicAt (fun w : ℂ => stripPoissonKernel w.re w.im) z := by
  have he : (fun w : ℂ => stripPoissonKernel w.re w.im) =ᶠ[𝓝 z]
      (fun w : ℂ => (stripCauchyKernel w).im) := by
    have hh : ∀ᶠ w : ℂ in 𝓝 z, w.re ∈ Ioo (0 : ℝ) 1 :=
      (Complex.continuous_re.tendsto z).eventually (Ioo_mem_nhds hz0 hz1)
    filter_upwards [hh] with w hw
    have hid := stripCauchyKernel_im hw.1 hw.2 w.im
    simpa only [Complex.re_add_im] using hid.symm
  exact (harmonicAt_congr_nhds he).mpr (stripCauchyKernel_analyticAt hz0 hz1).harmonicAt_im

/-- Explicit complex derivative of the analytic strip kernel.
Auxiliary differentiation input for Rademacher page 193 display 2.52. -/
theorem stripCauchyKernel_hasDerivAt {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    HasDerivAt stripCauchyKernel
      (((Real.pi : ℂ) * Complex.I) * Complex.exp ((Real.pi : ℂ) * Complex.I * z) /
        (1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z)) ^ 2) z := by
  have hi : 0 < (Complex.exp ((Real.pi : ℂ) * Complex.I * z)).im := by
    rw [Complex.exp_im]
    apply mul_pos (Real.exp_pos _)
    have hh : (((Real.pi : ℂ) * Complex.I) * z).im = Real.pi * z.re := by simp
    rw [hh]
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hz0) (by nlinarith [Real.pi_pos])
  have hn : 1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.zero_im] at hh
    linarith
  have hexp := (Complex.hasDerivAt_exp (((Real.pi : ℂ) * Complex.I) * z)).comp z
    ((hasDerivAt_id z).const_mul ((Real.pi : ℂ) * Complex.I))
  have hd := ((hasDerivAt_const z (1 : ℂ)).sub hexp).inv hn
  convert hd using 1
  · ext w
    rfl
  · simp only [Function.comp_def, Pi.sub_apply, mul_one, zero_sub, neg_neg]
    ring

/-- The derivative norm is pi over sine times the real strip Poisson kernel.
Auxiliary local domination identity for Rademacher page 193 display 2.52. -/
theorem stripCauchyKernel_deriv_norm {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    ‖deriv stripCauchyKernel z‖ =
      (Real.pi / Real.sin (Real.pi * z.re)) * stripPoissonKernel z.re z.im := by
  have hs := (kernel_parameter_pos hz0 hz1).1
  let w : ℂ := 1 - Complex.exp ((Real.pi : ℂ) * Complex.I * z)
  have him : -w.im = Real.exp (-Real.pi * z.im) * Real.sin (Real.pi * z.re) := by
    dsimp [w]
    simp [Complex.exp_im]
  have hn : (stripCauchyKernel z).im =
      (Real.exp (-Real.pi * z.im) * Real.sin (Real.pi * z.re)) / Complex.normSq w := by
    change w⁻¹.im = _
    rw [Complex.inv_im, him]
  have hk := stripCauchyKernel_im hz0 hz1 z.im
  rw [Complex.re_add_im] at hk
  rw [← hk, hn, (stripCauchyKernel_hasDerivAt hz0 hz1).deriv]
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_exp, norm_pow]
  have hre : (((Real.pi : ℂ) * Complex.I) * z).re = -Real.pi * z.im := by simp
  rw [hre, ← Complex.normSq_eq_norm_sq]
  change Real.pi * Real.exp (-Real.pi * z.im) / Complex.normSq w = _
  field_simp [hs.ne']

/-- Exponential decay of the complex kernel derivative at every interior horizontal parameter.
Auxiliary domination estimate for Rademacher page 193 display 2.52. -/
theorem stripCauchyKernel_deriv_bound {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    ‖deriv stripCauchyKernel z‖ ≤
      (Real.pi / (1 - |Real.cos (Real.pi * z.re)|)) * Real.exp (-Real.pi * |z.im|) := by
  have hp := kernel_parameter_pos hz0 hz1
  rw [stripCauchyKernel_deriv_norm hz0 hz1]
  have hk := stripPoissonKernel_exp_bound hz0 hz1 z.im
  rw [Real.norm_eq_abs, abs_of_pos (stripPoissonKernel_pos hz0 hz1 z.im)] at hk
  calc
    _ ≤ (Real.pi / Real.sin (Real.pi * z.re)) *
        ((Real.sin (Real.pi * z.re) / (1 - |Real.cos (Real.pi * z.re)|)) * Real.exp (-Real.pi * |z.im|)) :=
      mul_le_mul_of_nonneg_left hk (div_pos Real.pi_pos hp.1).le
    _ = (Real.pi / (1 - |Real.cos (Real.pi * z.re)|)) * Real.exp (-Real.pi * |z.im|) := by
      field_simp [hp.1.ne', hp.2.ne']

end LeanLab.BHP1997.Decomp560e
