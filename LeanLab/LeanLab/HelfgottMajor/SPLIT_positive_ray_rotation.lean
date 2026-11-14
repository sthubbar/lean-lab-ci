import LeanLab.HelfgottMajor.Decomp511b
import Mathlib

/-!
Split of `Decomp511b.positive_ray_rotation`, the contour replacement by the rotated ray `C'`
before displays 3.65 and 3.66 of page 26 of the source, into one leaf per analytic step.

The shape of the statement is the angle independence of the line integral of
`z ^ (s - 1) * exp (-z ^ 2 / 2 + 2 * pi * I * delta * z)` along the ray of angle `theta`,
together with the identification of the `theta = 0` ray with `gaussianMellin`. Writing the
ray parametrization `z = r * exp (I * theta)` gives the prefactor `exp (I * theta * s)` and
the kernel `rotatedKernel`, whose norm is already evaluated in this module.

The leaves are: the `theta = 0` identification, the continuity of the angle family at the
left endpoint `0`, the vanishing of its angle derivative on the open interval, and the
derivative of the angle prefactor. The assembly is angle constancy on the open interval
combined with the endpoint limit and the theta zero identification.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_positive_ray_rotation

open Real MeasureTheory Filter Set
open LeanLab.HelfgottArcs SplitGaussian123
open LeanLab.HelfgottMajor.Decomp511b
open scoped Topology

/-- LEAF zero angle identification. At angle zero the rotated kernel is exactly the twisted
Gaussian Mellin integrand, so the rotated ray integral is `gaussianMellin` itself. -/
theorem zero_angle_ray_eq_mellin (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) :
    (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x) = gaussianMellin δ s := by
  unfold rotatedKernel gaussianMellin
  simp only [mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, mul_one, smul_eq_mul]
  congr 1
  rw [show e (δ * x) = Complex.exp (((2 * π * δ * x : ℝ) : ℂ) * Complex.I) by
    simp only [e]
    push_cast
    ring_nf]
  rw [Complex.ofReal_exp, ← Complex.exp_add]

/-- LEAF endpoint continuity of the angle family. As the angle decreases to zero from above,
the normalized rotated ray integral tends to its value at angle zero. This is the dominated
convergence step, with the Gaussian majorant coming from `rotatedKernel_norm`. -/
theorem angle_family_tendsto_zero (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) :
    Tendsto (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ φ s x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x)) := by
  set C : ℝ := 2 * π * |δ| with hC
  set B : ℝ := Real.exp |s.im| * Real.exp (2 * C ^ 2) with hB
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hmain : Tendsto (fun φ : ℝ => ∫ x : ℝ in Ioi (0 : ℝ),
      (Complex.exp ((φ : ℂ) * Complex.I * s) * rotatedKernel δ φ s x))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => B * (x ^ (s.re - 1) * Real.exp (-(1 / 8 : ℝ) * x ^ 2)))
      ?_ ?_ ?_ ?_
    · filter_upwards with φ
      have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) :=
        Complex.continuous_ofReal.continuousOn.cpow_const
          (fun x hx => Complex.ofReal_mem_slitPlane.mpr hx)
      have he : Continuous (fun x : ℝ => Complex.exp
          (((-x ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
            ((2 * π * δ * x : ℝ) : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I))) := by
        fun_prop
      have hk : ContinuousOn (rotatedKernel δ φ s) (Ioi 0) := hc.mul he.continuousOn
      exact (continuousOn_const.mul hk).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < π / 8 by positivity)).filter_mono
          nhdsWithin_le_nhds] with φ hφ0 hφ1
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have hφ0pos : (0 : ℝ) < φ := hφ0
      have hphi1 : φ ≤ 1 := by nlinarith [Real.pi_lt_four, hφ1]
      have hcos : (1 / 2 : ℝ) ≤ Real.cos (2 * φ) := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * φ) (y := π / 3)
          (by linarith) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_lt_four, hφ1])
        simpa [Real.cos_pi_div_three] using h
      have hsin0 : 0 ≤ Real.sin φ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hφ0pos.le (by nlinarith [Real.pi_lt_four, hφ1])
      have hsin1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
      have hexp1 : Real.exp (-φ * s.im) ≤ Real.exp |s.im| := by
        apply Real.exp_le_exp.mpr
        nlinarith [neg_abs_le s.im, abs_nonneg s.im, hφ0pos.le, hphi1]
      have hphase : -2 * π * δ * Real.sin φ * x ≤ C * x := by
        rw [hC]
        have h1 : -δ ≤ |δ| := neg_le_abs δ
        have h2 : -2 * π * δ * Real.sin φ ≤ 2 * π * |δ| * Real.sin φ := by
          nlinarith [mul_le_mul_of_nonneg_left h1
            (show (0 : ℝ) ≤ 2 * π * Real.sin φ by positivity)]
        have h3 : 2 * π * |δ| * Real.sin φ ≤ 2 * π * |δ| := by
          nlinarith [mul_le_mul_of_nonneg_left hsin1
            (show (0 : ℝ) ≤ 2 * π * |δ| by positivity)]
        nlinarith [h2, h3, hx0.le]
      have hA : -Real.cos (2 * φ) * x ^ 2 / 2 - 2 * π * δ * Real.sin φ * x ≤
          2 * C ^ 2 - x ^ 2 / 8 := by
        nlinarith [hcos, hphase, sq_nonneg (x - 4 * C), sq_nonneg x]
      rw [norm_mul, rotated_prefactor_norm, rotatedKernel_norm δ φ s x hx0]
      calc Real.exp (-φ * s.im) *
            (x ^ (s.re - 1) * Real.exp (-Real.cos (2 * φ) * x ^ 2 / 2 - 2 * π * δ * Real.sin φ * x))
          ≤ Real.exp |s.im| * (x ^ (s.re - 1) * Real.exp (2 * C ^ 2 - x ^ 2 / 8)) := by
            apply mul_le_mul hexp1 _ (by positivity) (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA) (rpow_nonneg hx0.le _)
        _ = B * (x ^ (s.re - 1) * Real.exp (-(1 / 8 : ℝ) * x ^ 2)) := by
            rw [show Real.exp (2 * C ^ 2 - x ^ 2 / 8) =
                Real.exp (2 * C ^ 2) * Real.exp (-(1 / 8 : ℝ) * x ^ 2) by
              rw [← Real.exp_add]; congr 1; ring]
            rw [hB]; ring
    · have hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-(1 / 8 : ℝ) * x ^ 2))
          (Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)
          (by linarith : (-1 : ℝ) < s.re - 1)
      exact hg.const_mul B
    · filter_upwards with x
      have h1 : Tendsto (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s))
          (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((0 : ℂ) * Complex.I * s))) := by
        have hlin : Continuous (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s)) := by
          fun_prop
        exact hlin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun φ : ℝ => rotatedKernel δ φ s x) (𝓝[>] (0 : ℝ))
          (𝓝 (rotatedKernel δ 0 s x)) := by
        refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
        unfold rotatedKernel
        fun_prop
      have h3 := h1.mul h2
      simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using h3
  have hEq : (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ φ s x))
      = fun φ : ℝ => ∫ x : ℝ in Ioi (0 : ℝ),
          Complex.exp ((φ : ℂ) * Complex.I * s) * rotatedKernel δ φ s x := by
    funext φ
    exact (integral_const_mul _ _).symm
  rw [hEq]
  exact hmain


/-- The rotated kernel is continuous on the positive axis. -/
private lemma rayKernel_continuousOn (δ θ : ℝ) (s : ℂ) :
    ContinuousOn (rotatedKernel δ θ s) (Ioi (0 : ℝ)) := by
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun x hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have he : Continuous (fun x : ℝ => Complex.exp
      (((-x ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) +
        ((2 * π * δ * x : ℝ) : ℂ) * Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) := by
    fun_prop
  exact hc.mul he.continuousOn

/-- Norm bound for the rotated kernel with the phase estimated by `2 * π * |δ| * x`. -/
private lemma rayKernel_norm_le (δ θ : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖rotatedKernel δ θ s x‖ ≤ x ^ (s.re - 1) *
      Real.exp (-Real.cos (2 * θ) * x ^ 2 / 2 + (2 * π * |δ|) * x) := by
  rw [rotatedKernel_norm δ θ s x hx]
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hx.le _)
  apply Real.exp_le_exp.mpr
  have h1 : -δ * Real.sin θ ≤ |δ| := by
    calc -δ * Real.sin θ = -(δ * Real.sin θ) := by ring
      _ ≤ |δ * Real.sin θ| := neg_le_abs _
      _ = |δ| * |Real.sin θ| := abs_mul _ _
      _ ≤ |δ| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one θ) (abs_nonneg δ)
      _ = |δ| := mul_one _
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * π * x by positivity)]

/-- Integrability of the rotated kernel on a ray whose angle has positive cosine. -/
private lemma rayKernel_integrableOn (δ θ : ℝ) (s : ℂ) (hσ : 0 < s.re)
    (hcos : 0 < Real.cos (2 * θ)) : IntegrableOn (rotatedKernel δ θ s) (Ioi 0) := by
  set a : ℝ := Real.cos (2 * θ) / 2 with ha
  have ha_pos : 0 < a := by rw [ha]; linarith
  set Cc : ℝ := 2 * π * |δ| with hCc
  have hCnn : 0 ≤ Cc := by rw [hCc]; positivity
  set K : ℝ := Cc ^ 2 / (2 * a) with hK
  have hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-(a / 2) * x ^ 2))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (b := a / 2) (by linarith)
      (by linarith : (-1 : ℝ) < s.re - 1)
  have hgb : IntegrableOn (fun x : ℝ =>
      Real.exp K * (x ^ (s.re - 1) * Real.exp (-(a / 2) * x ^ 2))) (Ioi 0) :=
    hg.const_mul (Real.exp K)
  refine hgb.mono' ((rayKernel_continuousOn δ θ s).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hstep : ‖rotatedKernel δ θ s x‖ ≤ x ^ (s.re - 1) *
      Real.exp (-a * x ^ 2 + Cc * x) := by
    have h := rayKernel_norm_le δ θ s hx0
    rw [hCc]
    refine h.trans_eq ?_
    congr 2
    rw [ha]
    ring
  have hKmul : 2 * a * K = Cc ^ 2 := by
    rw [hK]
    field_simp
  have hquad : -a * x ^ 2 + Cc * x ≤ K - a / 2 * x ^ 2 := by
    nlinarith [sq_nonneg (a * x - Cc), sq_nonneg x]
  have hexp : Real.exp (-a * x ^ 2 + Cc * x) ≤ Real.exp (K - a / 2 * x ^ 2) :=
    Real.exp_le_exp.mpr hquad
  refine hstep.trans ?_
  calc x ^ (s.re - 1) * Real.exp (-a * x ^ 2 + Cc * x)
      ≤ x ^ (s.re - 1) * Real.exp (K - a / 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (rpow_nonneg hx0.le _)
    _ = Real.exp K * (x ^ (s.re - 1) * Real.exp (-(a / 2) * x ^ 2)) := by
        rw [show Real.exp (K - a / 2 * x ^ 2) =
          Real.exp K * Real.exp (-(a / 2) * x ^ 2) by
            rw [← Real.exp_add]; congr 1; ring]
        ring

/-- The complex power steps up by one on multiplication with a positive real. -/
private lemma cpow_self_step {x : ℝ} (s : ℂ) (hx : 0 < x) :
    (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * x := by
  have h : (x : ℂ) ^ s = (x : ℂ) ^ ((s - 1) + 1) := by
    congr 1
    ring
  rw [h, Complex.cpow_add _ _ (by exact_mod_cast hx.ne'), Complex.cpow_one]

/-- The angle derivative of the normalized rotated kernel at a fixed ray point. -/
private lemma angleKernel_hasDerivAt (δ : ℝ) (s : ℂ) (ψ : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * s) * rotatedKernel δ t s x)
      ((x : ℂ) ^ (s - 1) *
        Complex.exp ((ψ : ℂ) * Complex.I * s +
            (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
            (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) *
        (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
            Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
            (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)))) ψ := by
  have hfun : (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * s) * rotatedKernel δ t s x)
      = fun t : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp ((t : ℂ) * Complex.I * s +
            (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) +
            (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
              Complex.exp ((t : ℂ) * Complex.I)) := by
    funext t
    unfold rotatedKernel
    rw [← mul_assoc, mul_comm (Complex.exp ((t : ℂ) * Complex.I * s)) ((x : ℂ) ^ (s - 1)),
      mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun]
  have hbase : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I * s) (Complex.I * s) ψ := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, mul_assoc] using
      (Complex.ofRealCLM.hasDerivAt (x := ψ)).mul_const (Complex.I * s)
  have hA1 : HasDerivAt
      (fun t : ℝ => (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I))
      ((-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))) ψ := by
    have h2 : HasDerivAt (fun t : ℝ => (((2 * t : ℝ)) : ℂ) * Complex.I)
        ((2 : ℂ) * Complex.I) ψ := by
      have h := (((hasDerivAt_id ψ).const_mul (2 : ℝ)).ofReal_comp).mul_const Complex.I
      simpa using h
    have h3 := h2.cexp
    have h4 := h3.const_mul (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)
    convert h4 using 1
    ring
  have hA2 : HasDerivAt
      (fun t : ℝ => (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        Complex.exp ((t : ℂ) * Complex.I))
      ((((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) ψ := by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (Complex.I) ψ := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := ψ)).mul_const Complex.I
      simpa using h
    have h3 := h2.cexp
    have h4 := h3.const_mul ((((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I)
    convert h4 using 1
    ring
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I * s +
      (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) +
      (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((t : ℂ) * Complex.I))
      (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
          Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
        (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
          (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) ψ :=
    (hbase.add hA1).add hA2
  have hfinal := harg.cexp
  convert hfinal.const_mul ((x : ℂ) ^ (s - 1)) using 1
  ring

/-- The ray antiderivative `x ^ s` times the normalized exponential, differentiated in `x`. -/
private lemma rayAntideriv_hasDerivAt (δ : ℝ) (s : ℂ) (ψ : ℝ) (hs : s ≠ 0) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s * Complex.exp ((ψ : ℂ) * Complex.I * s +
        (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
        (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)))
      (s * (x : ℂ) ^ (s - 1) * Complex.exp ((ψ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) +
        (x : ℂ) ^ s * Complex.exp ((ψ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) *
        ((-(1 / 2 : ℂ) * ((2 : ℂ) * (x : ℂ))) *
            Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) x := by
  have hpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x :=
    hasDerivAt_ofReal_cpow_const hx.ne' hs
  have hbase : HasDerivAt (fun _ : ℝ => (ψ : ℂ) * Complex.I * s) 0 x := hasDerivAt_const x _
  have hA1 : HasDerivAt
      (fun y : ℝ => (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))
      ((-(1 / 2 : ℂ) * ((2 : ℂ) * (x : ℂ))) *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) x := by
    have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) ((2 : ℂ) * (x : ℂ)) x := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := x)).pow 2
      convert h using 1
      · funext y
        simp
      · norm_num
    have h4 := (hsq.const_mul (-(1 / 2 : ℂ))).mul_const
      (Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))
    exact h4
  have hA2 : HasDerivAt
      (fun y : ℝ => (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I *
        Complex.exp ((ψ : ℂ) * Complex.I))
      ((((2 * π * δ : ℝ)) : ℂ) * Complex.I *
        Complex.exp ((ψ : ℂ) * Complex.I)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ))
        (((2 * π * δ : ℝ)) : ℂ) x := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (((2 * π * δ : ℝ)) : ℂ)
      simpa using h
    have h4 := ((h1.mul_const Complex.I).mul_const
      (Complex.exp ((ψ : ℂ) * Complex.I)))
    exact h4
  have harg := (hbase.add hA1).add hA2
  have hexp := harg.cexp
  convert hpow.mul hexp using 1
  rw [show s - 1 = -1 + s by ring]
  simp only [Pi.add_apply]
  ring

/-- The angle derivative of the normalized kernel is `I` times the ray antiderivative. -/
private lemma angleKernelDeriv_eq (δ : ℝ) (s : ℂ) (ψ : ℝ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) * Complex.exp ((ψ : ℂ) * Complex.I * s +
        (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
        (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) *
      (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
          Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
        (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
          (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) =
    Complex.I * (s * (x : ℂ) ^ (s - 1) * Complex.exp ((ψ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) +
        (x : ℂ) ^ s * Complex.exp ((ψ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) *
        ((-(1 / 2 : ℂ) * ((2 : ℂ) * (x : ℂ))) *
            Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) := by
  rw [cpow_self_step s hx]
  ring

/-- The normalized rotated kernel written as a single exponential. -/
private lemma angleKernel_eq (δ : ℝ) (s : ℂ) (ψ x : ℝ) :
    Complex.exp ((ψ : ℂ) * Complex.I * s) * rotatedKernel δ ψ s x
      = (x : ℂ) ^ (s - 1) * Complex.exp ((ψ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)) := by
  unfold rotatedKernel
  rw [← mul_assoc, mul_comm (Complex.exp ((ψ : ℂ) * Complex.I * s)) ((x : ℂ) ^ (s - 1)),
    mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Norm bound for the normalized rotated kernel. -/
private lemma angleKernel_norm_le (δ : ℝ) (s : ℂ) (ψ x : ℝ) (hx : 0 < x) :
    ‖Complex.exp ((ψ : ℂ) * Complex.I * s) * rotatedKernel δ ψ s x‖ ≤
      x ^ (s.re - 1) * Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im +
        (2 * π * |δ|) * x) := by
  rw [norm_mul, rotated_prefactor_norm]
  refine (mul_le_mul_of_nonneg_left (rayKernel_norm_le δ ψ s hx) (Real.exp_pos _).le).trans_eq ?_
  rw [show Real.exp (-ψ * s.im) *
      (x ^ (s.re - 1) * Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 + (2 * π * |δ|) * x)) =
      x ^ (s.re - 1) * Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im +
        (2 * π * |δ|) * x) by
    rw [show Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im + (2 * π * |δ|) * x) =
      Real.exp (-ψ * s.im) * Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 + (2 * π * |δ|) * x) by
      rw [← Real.exp_add]; congr 1; ring]
    ring]

/-- Norm bound for the angle-derivative factor. -/
private lemma derivFactor_norm_le (δ : ℝ) (s : ℂ) (ψ x : ℝ) (hx : 0 < x) :
    ‖Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
      (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))‖
      ≤ (‖s‖ + 1 + 2 * π * |δ|) * (1 + x ^ 2) := by
  have hIs : ‖Complex.I * s‖ = ‖s‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have he2 : ‖Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have he1 : ‖Complex.exp ((ψ : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hA1 : ‖(2 : ℂ) * Complex.I * Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)‖ = 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, he2]
    norm_num
  have hB1 : ‖(-(1 / 2 : ℂ) * (x : ℂ) ^ 2)‖ = x ^ 2 / 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    rw [show ‖(-(1 / 2 : ℂ))‖ = 1 / 2 by norm_num]
    ring
  have hP1 : ‖(-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
      Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))‖ = x ^ 2 := by
    rw [norm_mul, hA1, hB1]
    ring
  have hAabs : ‖(((2 * π * δ : ℝ)) : ℂ)‖ = 2 * π * |δ| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos pi_pos]
  have hP2 : ‖(((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
      (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))‖ = 2 * π * |δ| * x := by
    rw [norm_mul, norm_mul, norm_mul, hAabs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx, norm_mul, Complex.norm_I, one_mul, he1, mul_one]
    ring
  have htri : ‖Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
      (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))‖
      ≤ ‖Complex.I * s‖ + ‖(-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
          Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))‖ +
        ‖(((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
          (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))‖ := by
    have h1 := norm_add_le (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I))) ((((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I)))
    have h2 := norm_add_le (Complex.I * s) ((-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)))
    linarith
  refine htri.trans ?_
  rw [hIs, hP1, hP2]
  have h1 : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hexp : (‖s‖ + 1 + 2 * π * |δ|) * (1 + x ^ 2) =
      ‖s‖ + ‖s‖ * x ^ 2 + 1 + x ^ 2 + 2 * π * |δ| + 2 * π * |δ| * x ^ 2 := by ring
  rw [hexp]
  nlinarith [h1, mul_le_mul_of_nonneg_left h1 (norm_nonneg s),
    mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * π * |δ| by positivity),
    sq_nonneg x, norm_nonneg s, abs_nonneg δ, pi_pos]

set_option maxHeartbeats 1600000 in
/-- LEAF vanishing of the angle derivative. The normalized rotated ray integral has zero
derivative at every interior angle, which is the angle independence of the contour integral
of the twisted Gaussian exponential. -/
theorem angle_family_deriv_zero (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) (φ : ℝ)
    (hφ : φ ∈ Ioo (0 : ℝ) (π / 4)) :
    HasDerivAt (fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ ψ s x)) 0 φ := by
  have hφ0 : (0 : ℝ) < φ := hφ.1
  have hφ1 : φ < π / 4 := hφ.2
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simpa using hσ
  have hcosφ : 0 < Real.cos (2 * φ) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hprod : (fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ ψ s x))
      = fun ψ : ℝ => ∫ x : ℝ in Ioi (0 : ℝ),
          Complex.exp ((ψ : ℂ) * Complex.I * s) * rotatedKernel δ ψ s x := by
    funext ψ
    exact (integral_const_mul _ _).symm
  rw [hprod]
  set a : ℝ := Real.cos (φ + π / 4) / 2 with ha
  have ha_pos : 0 < a := by
    have h1 : 0 < Real.cos (φ + π / 4) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]
    rw [ha]
    linarith
  set Cc : ℝ := 2 * π * |δ| with hCc
  have hCnn : 0 ≤ Cc := by rw [hCc]; positivity
  set K : ℝ := Cc ^ 2 / (2 * a) with hK
  have hKmul : 2 * a * K = Cc ^ 2 := by
    rw [hK]
    field_simp
  set Bb : ℝ := Real.exp (π / 4 * |s.im|) * Real.exp K * (‖s‖ + 1 + Cc) with hBb
  have hBnn : 0 ≤ Bb := by rw [hBb]; positivity
  set bound : ℝ → ℝ := fun x => Bb * (x ^ (s.re - 1) * Real.exp (-(a / 2) * x ^ 2) +
    x ^ (s.re + 1) * Real.exp (-(a / 2) * x ^ 2)) with hbound
  set F : ℝ → ℝ → ℂ := fun ψ x => Complex.exp ((ψ : ℂ) * Complex.I * s) *
    rotatedKernel δ ψ s x with hF
  set F' : ℝ → ℝ → ℂ := fun ψ x => F ψ x *
    (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
        Complex.exp (((2 * ψ : ℝ) : ℂ) * Complex.I)) +
      (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
        (Complex.I * Complex.exp ((ψ : ℂ) * Complex.I))) with hF'
  -- integrability of the majorant
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hbound, hBb]
    have h1 : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * Real.exp (-(a / 2) * x ^ 2))
        (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by linarith) (by linarith : (-1 : ℝ) < s.re - 1)
    have h2 : IntegrableOn (fun x : ℝ => x ^ (s.re + 1) * Real.exp (-(a / 2) * x ^ 2))
        (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by linarith) (by linarith : (-1 : ℝ) < s.re + 1)
    exact (h1.add h2).const_mul _
  -- the pointwise bound on the angle derivative
  have hF'_le : ∀ ψ ∈ Ioo (φ / 2) ((φ + π / 4) / 2), ∀ x ∈ Ioi (0 : ℝ), ‖F' ψ x‖ ≤ bound x := by
    intro ψ hψ x hx
    have hx0 : 0 < x := hx
    have hψ0 : 0 < ψ := by linarith [hψ.1]
    have hψu : ψ < π / 4 := by
      have := hψ.2
      nlinarith [Real.pi_pos]
    have hcos : 2 * a ≤ Real.cos (2 * ψ) := by
      rw [ha]
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * ψ) (y := φ + π / 4)
        (by linarith) (by linarith [Real.pi_pos]) (by linarith [hψ.2])
      linarith
    have hexppsi : Real.exp (-ψ * s.im) ≤ Real.exp (π / 4 * |s.im|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [neg_abs_le s.im, abs_nonneg s.im, hψ0.le, hψu.le, Real.pi_lt_four]
    have hexpCc : Real.exp (Cc * x) ≤ Real.exp K * Real.exp (a / 2 * x ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (a * x - Cc), hKmul, ha_pos.le]
    have hkern := angleKernel_norm_le δ s ψ x hx0
    have hfac := derivFactor_norm_le δ s ψ x hx0
    rw [hF', hF, norm_mul]
    refine (mul_le_mul hkern hfac (norm_nonneg _) (by positivity)).trans ?_
    rw [hCc] at *
    have hcomb : x ^ (s.re - 1) *
        Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im + (2 * π * |δ|) * x) *
          ((‖s‖ + 1 + 2 * π * |δ|) * (1 + x ^ 2)) ≤
        Real.exp (π / 4 * |s.im|) * Real.exp K * (‖s‖ + 1 + 2 * π * |δ|) *
          ((x ^ (s.re - 1) + x ^ (s.re + 1)) * Real.exp (-(a / 2) * x ^ 2)) := by
      have hE : Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im + (2 * π * |δ|) * x) ≤
          Real.exp (π / 4 * |s.im|) * Real.exp K * Real.exp (-(a / 2) * x ^ 2) := by
        rw [show Real.exp (π / 4 * |s.im|) * Real.exp K * Real.exp (-(a / 2) * x ^ 2) =
          Real.exp (π / 4 * |s.im| + K + -(a / 2) * x ^ 2) by
            rw [← Real.exp_add, ← Real.exp_add]]
        apply Real.exp_le_exp.mpr
        have h1 : -Real.cos (2 * ψ) * x ^ 2 / 2 ≤ -a * x ^ 2 := by nlinarith
        have h2 : -ψ * s.im ≤ π / 4 * |s.im| := by nlinarith [neg_abs_le s.im, abs_nonneg s.im, hψ0.le, hψu.le, Real.pi_lt_four]
        have h3 : (2 * π * |δ|) * x ≤ K + a / 2 * x ^ 2 := by
          nlinarith [sq_nonneg (a * x - Cc), hKmul, ha_pos.le]
        linarith
      have hpow : x ^ (s.re - 1) * (1 + x ^ 2) = x ^ (s.re - 1) + x ^ (s.re + 1) := by
        rw [mul_add, mul_one, ← Real.rpow_two, ← Real.rpow_add hx0,
          show s.re - 1 + 2 = s.re + 1 by ring]
      calc x ^ (s.re - 1) *
            Real.exp (-Real.cos (2 * ψ) * x ^ 2 / 2 - ψ * s.im + (2 * π * |δ|) * x) *
              ((‖s‖ + 1 + 2 * π * |δ|) * (1 + x ^ 2))
          ≤ x ^ (s.re - 1) * (Real.exp (π / 4 * |s.im|) * Real.exp K *
              Real.exp (-(a / 2) * x ^ 2)) * ((‖s‖ + 1 + 2 * π * |δ|) * (1 + x ^ 2)) := by
            apply mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE (rpow_nonneg hx0.le _)) (by positivity)
        _ = Real.exp (π / 4 * |s.im|) * Real.exp K * (‖s‖ + 1 + 2 * π * |δ|) *
              ((x ^ (s.re - 1) + x ^ (s.re + 1)) * Real.exp (-(a / 2) * x ^ 2)) := by
            rw [← hpow]; ring
    refine hcomb.trans_eq ?_
    simp only [hbound, hBb]
    ring
  -- the parametrized derivative
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (x₀ := φ)
    (s := Ioo (φ / 2) ((φ + π / 4) / 2)) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (by linarith) (by linarith [Real.pi_pos]))
    (by
      filter_upwards with ψ
      rw [hF]
      exact (continuousOn_const.mul (rayKernel_continuousOn δ ψ s)).aestronglyMeasurable
        measurableSet_Ioi)
    (by
      rw [hF]
      exact (rayKernel_integrableOn δ φ s hσ hcosφ).const_mul _)
    (by
      rw [hF', hF]
      have hc : ContinuousOn (fun x : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s) *
          rotatedKernel δ φ s x) (Ioi 0) :=
        continuousOn_const.mul (rayKernel_continuousOn δ φ s)
      have hfac : Continuous (fun x : ℝ => Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
            Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I)) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
            (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))) := by
        fun_prop
      exact (hc.mul hfac.continuousOn).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro ψ hψ
      exact hF'_le ψ hψ x hx)
    hbound_int
    (by
      filter_upwards with x
      intro ψ hψ
      have h := angleKernel_hasDerivAt δ s ψ x
      refine h.congr_deriv ?_
      simp only [hF, hF', angleKernel_eq δ s ψ x])
  obtain ⟨hint, hder⟩ := hmain
  -- the integral of the angle derivative vanishes
  have hzero : (∫ x : ℝ in Ioi (0 : ℝ), F' φ x) = 0 := by
    set D : ℝ → ℂ := fun y => Complex.I * ((y : ℂ) ^ s * Complex.exp ((φ : ℂ) * Complex.I * s +
      (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
      (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I)))
      with hD
    have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt D (F' φ x) x := by
      intro x hx
      have h1 : HasDerivAt
          (fun y : ℝ => (y : ℂ) ^ s * Complex.exp ((φ : ℂ) * Complex.I * s +
            (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
            (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I *
              Complex.exp ((φ : ℂ) * Complex.I)))
          (s * (x : ℂ) ^ (s - 1) * Complex.exp ((φ : ℂ) * Complex.I * s +
              (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
              (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
                Complex.exp ((φ : ℂ) * Complex.I)) +
            (x : ℂ) ^ s * Complex.exp ((φ : ℂ) * Complex.I * s +
              (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
              (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
                Complex.exp ((φ : ℂ) * Complex.I)) *
              ((-(1 / 2 : ℂ) * ((2 : ℂ) * (x : ℂ))) *
                  Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
                (((2 * π * δ : ℝ)) : ℂ) * Complex.I *
                  Complex.exp ((φ : ℂ) * Complex.I))) x :=
        rayAntideriv_hasDerivAt δ s φ hs0 hx
      have h2 := h1.const_mul Complex.I
      rw [hD]
      refine h2.congr_deriv ?_
      rw [show F' φ x = (x : ℂ) ^ (s - 1) * Complex.exp ((φ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
            Complex.exp ((φ : ℂ) * Complex.I)) *
        (Complex.I * s + (-(1 / 2 : ℂ) * (x : ℂ) ^ 2) * ((2 : ℂ) * Complex.I *
            Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I)) +
          (((2 * π * δ : ℝ)) : ℂ) * (x : ℂ) * Complex.I *
            (Complex.I * Complex.exp ((φ : ℂ) * Complex.I))) from by
        simp only [hF, hF', angleKernel_eq δ s φ x]]
      exact (angleKernelDeriv_eq δ s φ hx).symm
    have hcont : ContinuousWithinAt D (Ici (0 : ℝ)) 0 := by
      rw [hD]
      have hp : Tendsto (fun y : ℝ => (y : ℂ) ^ s) (𝓝[Ici (0 : ℝ)] 0) (𝓝 ((((0 : ℝ)) : ℂ) ^ s)) :=
        (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hσ)).tendsto.mono_left
          nhdsWithin_le_nhds
      have hec : Continuous (fun y : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I))) := by
        fun_prop
      have he : Tendsto (fun y : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I)))
          (𝓝[Ici (0 : ℝ)] 0) (𝓝 (Complex.exp ((φ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (((0 : ℝ)) : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (((0 : ℝ)) : ℂ) * Complex.I *
            Complex.exp ((φ : ℂ) * Complex.I)))) :=
        hec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact (hp.mul he).const_mul Complex.I
    have hlim : Tendsto D atTop (𝓝 0) := by
      rw [hD]
      rw [show (0 : ℂ) = Complex.I * 0 by ring]
      refine Tendsto.const_mul Complex.I ?_
      have hb : ∀ᶠ y : ℝ in atTop, ‖(y : ℂ) ^ s * Complex.exp ((φ : ℂ) * Complex.I * s +
          (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
          (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I *
            Complex.exp ((φ : ℂ) * Complex.I))‖ ≤
          Real.exp (π / 4 * |s.im|) * Real.exp K * ((y ^ s.re) *
            Real.exp (-(a / 2) * y ^ 2)) := by
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
        have hy0 : 0 < y := hy
        have h1 : ‖Complex.exp ((φ : ℂ) * Complex.I * s) * rotatedKernel δ φ s y‖ ≤
            y ^ (s.re - 1) * Real.exp (-Real.cos (2 * φ) * y ^ 2 / 2 - φ * s.im +
              (2 * π * |δ|) * y) := angleKernel_norm_le δ s φ y hy0
        rw [show (y : ℂ) ^ s * Complex.exp ((φ : ℂ) * Complex.I * s +
            (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) * Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) +
            (((2 * π * δ : ℝ)) : ℂ) * (y : ℂ) * Complex.I * Complex.exp ((φ : ℂ) * Complex.I)) =
            (Complex.exp ((φ : ℂ) * Complex.I * s) * rotatedKernel δ φ s y) * (y : ℂ) from by
          rw [angleKernel_eq δ s φ y, cpow_self_step s hy0]
          ring]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
        have hE : Real.exp (-Real.cos (2 * φ) * y ^ 2 / 2 - φ * s.im + (2 * π * |δ|) * y) ≤
            Real.exp (π / 4 * |s.im|) * Real.exp K * Real.exp (-(a / 2) * y ^ 2) := by
          rw [show Real.exp (π / 4 * |s.im|) * Real.exp K * Real.exp (-(a / 2) * y ^ 2) =
            Real.exp (π / 4 * |s.im| + K + -(a / 2) * y ^ 2) by
              rw [← Real.exp_add, ← Real.exp_add]]
          apply Real.exp_le_exp.mpr
          have hcosφ2 : Real.cos (φ + π / 4) ≤ Real.cos (2 * φ) :=
            Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * φ) (y := φ + π / 4)
              (by linarith) (by linarith [Real.pi_pos]) (by linarith)
          have h1 : -Real.cos (2 * φ) * y ^ 2 / 2 ≤ -a * y ^ 2 := by
            rw [ha]
            nlinarith [hcosφ2, sq_nonneg y]
          have h2 : -φ * s.im ≤ π / 4 * |s.im| := by
            nlinarith [neg_abs_le s.im, abs_nonneg s.im, hφ0.le, hφ1.le, Real.pi_lt_four]
          have h3 : (2 * π * |δ|) * y ≤ K + a / 2 * y ^ 2 := by
            nlinarith [sq_nonneg (a * y - Cc), hKmul, ha_pos.le]
          linarith
        have hpow : y ^ (s.re - 1) * y = y ^ s.re := by
          conv_rhs => rw [show s.re = (s.re - 1) + 1 by ring]
          rw [Real.rpow_add hy0, Real.rpow_one]
        calc ‖Complex.exp ((φ : ℂ) * Complex.I * s) * rotatedKernel δ φ s y‖ * y
            ≤ (y ^ (s.re - 1) * Real.exp (-Real.cos (2 * φ) * y ^ 2 / 2 - φ * s.im +
                (2 * π * |δ|) * y)) * y := mul_le_mul_of_nonneg_right h1 hy0.le
          _ ≤ (y ^ (s.re - 1) * (Real.exp (π / 4 * |s.im|) * Real.exp K *
                Real.exp (-(a / 2) * y ^ 2))) * y :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hE (rpow_nonneg hy0.le _)) hy0.le
          _ = Real.exp (π / 4 * |s.im|) * Real.exp K * (y ^ s.re *
                Real.exp (-(a / 2) * y ^ 2)) := by
              rw [← hpow]; ring
      have hlim0 : Tendsto (fun y : ℝ => Real.exp (π / 4 * |s.im|) * Real.exp K *
          ((y ^ s.re) * Real.exp (-(a / 2) * y ^ 2))) atTop (𝓝 0) := by
        have hb0 : Tendsto (fun y : ℝ => y ^ s.re * Real.exp (-(a / 2) * y ^ 2))
            atTop (𝓝 0) := by
          have hexp : Tendsto (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp
              (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
          exact (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
            (by linarith : (0 : ℝ) < a / 2) s.re).tendsto_zero_of_tendsto hexp
        simpa using (hb0.const_mul (Real.exp (π / 4 * |s.im|) * Real.exp K))
      refine squeeze_zero_norm' hb ?_
      simpa using hlim0
    have hFt := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
    have hD0 : D 0 = 0 := by
      rw [hD]
      simp only [Complex.ofReal_zero, Complex.zero_cpow hs0]
      ring
    rw [hD0] at hFt
    simpa using hFt
  rw [hzero] at hder
  exact hder


/-- LEAF derivative of the angle prefactor `exp (I * theta * s)` in the real angle. -/
theorem angle_prefactor_hasDerivAt (s : ℂ) (φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s))
      (Complex.I * s * Complex.exp ((φ : ℂ) * Complex.I * s)) φ := by
  have hlin : HasDerivAt (fun ψ : ℝ => (ψ : ℂ) * Complex.I * s)
      (Complex.I * s) φ := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, mul_assoc] using
      (Complex.ofRealCLM.hasDerivAt (x := φ)).mul_const (Complex.I * s)
  have h := hlin.cexp
  convert h using 1
  ring

/-- The contour replacement by the rotated ray, assembled from the four leaves above.
No hypothesis of the sealed statement is dropped and no leaf is used as its hypothesis. -/
theorem positive_ray_rotation_split (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    gaussianMellin δ s = Complex.exp ((θ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x) := by
  set F : ℝ → ℂ := fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s) *
    (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ ψ s x) with hF
  have hderiv : ∀ φ ∈ Ioo (0 : ℝ) (π / 4), HasDerivAt F 0 φ := by
    intro φ hφ
    rw [hF]
    exact angle_family_deriv_zero δ s hσ φ hφ
  have hdiff : DifferentiableOn ℝ F (Ioo (0 : ℝ) (π / 4)) := by
    intro φ hφ
    exact (hderiv φ hφ).differentiableAt.differentiableWithinAt
  have hzero : (Ioo (0 : ℝ) (π / 4)).EqOn (deriv F) 0 := by
    intro φ hφ
    exact (hderiv φ hφ).deriv
  have hconst : ∀ a ∈ Ioo (0 : ℝ) (π / 4), ∀ b ∈ Ioo (0 : ℝ) (π / 4), F a = F b :=
    fun a ha b hb => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ha hb
  have hlim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x)) := by
    rw [hF]
    exact angle_family_tendsto_zero δ s hσ
  have hlimθ : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F θ)) := by
    have hev : (fun _ : ℝ => F θ) =ᶠ[𝓝[>] (0 : ℝ)] F := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < π / 4 by linarith)).filter_mono
          nhdsWithin_le_nhds] with φ hφ hφ'
      exact (hconst φ ⟨hφ, hφ'⟩ θ ⟨hθ0, hθ1⟩).symm
    exact Tendsto.congr' hev tendsto_const_nhds
  have hEq : F θ = ∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x :=
    tendsto_nhds_unique hlimθ hlim0
  rw [← zero_angle_ray_eq_mellin δ s hσ, ← hEq, hF]

end LeanLab.HelfgottMajor.SPLIT_positive_ray_rotation
