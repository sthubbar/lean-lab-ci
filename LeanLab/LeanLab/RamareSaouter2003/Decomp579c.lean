import Mathlib
import LeanLab.PNTPort.StrongPNT.EulerMaclaurin
import LeanLab.RamareSaouter2003.Stirling518

/-!
Backlund pp. 363 and 364 display 59 and the Stieltjes estimate before display 60.
Lindelof pp. 97 through 99 displays 1, 3 and 5.
This independent file isolates the real Gamma identity from elementary errors.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp579c
open Real Complex Set MeasureTheory Filter
open scoped Topology

/-- Lindelof p. 97 display 3, the periodic fourth Bernoulli polynomial. -/
noncomputable def periodicB4 (x : ℝ) : ℝ :=
  (Int.fract x * (1 - Int.fract x)) ^ 2 - 1 / 30

/-- Lindelof p. 35, standard Bernoulli normalization checked against Mathlib. -/
theorem periodicB4_eq_mathlib (x : ℝ) :
    periodicB4 x = bernoulliFun 4 (Int.fract x) := by
  have h3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
  have h4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
  norm_num [periodicB4, bernoulliFun, Polynomial.bernoulli, Finset.sum_range_succ,
    h3, h4, Nat.choose]
  ring

/-- Lindelof p. 97 display 3, the standard periodic Bernoulli contribution.
The reciprocal-cube endpoint correction is retained separately in the identity. -/
noncomputable def stirlingRemainder (s : ℂ) : ℂ :=
  -(1 / 4 : ℂ) * ∫ x : ℝ in Ioi (0 : ℝ), (periodicB4 x : ℂ) / (s + x) ^ 4

/-- Backlund p. 363 display 59, a real logarithmic Euler-limit route.
Mathlib supplies convergence of the actual Gamma Euler sequence. -/
theorem gamma_log_norm_limit (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) :
    Tendsto (fun n : ℕ => Real.log ‖Complex.GammaSeq s n‖) atTop
      (𝓝 (Real.log ‖Complex.Gamma s‖)) := by
  have hg : ‖Complex.Gamma s‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero hs)
  exact (Real.continuousAt_log hg).tendsto.comp (Complex.GammaSeq_tendsto_Gamma s).norm

/-- Backlund p. 363 display 59, finite real Euler-product logarithm.
This identity avoids every choice of a logarithm of Gamma. -/
theorem gamma_seq_log_norm (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) (n : ℕ) (hn : 1 ≤ n) :
    Real.log ‖Complex.GammaSeq s n‖ =
      s.re * Real.log n + Real.log (n.factorial : ℝ) -
        ∑ j ∈ Finset.range (n + 1), Real.log ‖s + j‖ := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfactor (j : ℕ) : s + (j : ℂ) ≠ 0 := by
    simpa only [ne_eq, add_eq_zero_iff_eq_neg] using hs j
  have hprod : ∏ j ∈ Finset.range (n + 1), ‖s + j‖ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => norm_ne_zero_iff.mpr (hfactor j))
  have hpow : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos s
  have hfac : ‖(n.factorial : ℂ)‖ = (n.factorial : ℝ) := by
    simp only [Complex.norm_natCast]
  have hfpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpne : (n : ℝ) ^ s.re ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
  rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod, hpow, hfac]
  rw [Real.log_div (mul_ne_zero hpne hfpos.ne') hprod,
    Real.log_mul hpne hfpos.ne', Real.log_rpow hnpos,
    Real.log_prod (fun j hj => norm_ne_zero_iff.mpr (hfactor j))]

/-- Lindelof p. 87, differentiating the real Gamma logarithmic norm horizontally.
This route uses a real squared norm and has no logarithmic branch assumption. -/
theorem gamma_horizontal_log_derivative (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + t * I)‖)
      ((deriv Complex.Gamma ((x : ℂ) + t * I) /
        Complex.Gamma ((x : ℂ) + t * I)).re) x := by
  have hs : ∀ n : ℕ, (x : ℂ) + t * I ≠ -n := by
    intro n h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hg : Complex.Gamma ((x : ℂ) + t * I) ≠ 0 := Complex.Gamma_ne_zero hs
  have hshift : HasDerivAt (fun u : ℂ => u + (t : ℂ) * I) 1 (x : ℂ) :=
    (hasDerivAt_id _).add_const _
  have hG := (((Complex.differentiableAt_Gamma _ hs).hasDerivAt).comp (x : ℂ) hshift).comp_ofReal
  simp only [mul_one, Function.comp_def] at hG
  have hlog := (hG.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))).div_const 2
  have heq : (fun u : ℝ => Real.log (‖Complex.Gamma ((u : ℂ) + t * I)‖ ^ 2) / 2) =
      (fun u : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + t * I)‖) := by
    ext u
    rw [Real.log_pow]
    ring
  rw [heq] at hlog
  convert hlog using 1
  rw [Complex.inner, Complex.div_re, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Lindelof p. 87, horizontal integral of the actual real logarithmic derivative.
The Gamma function and its derivative are evaluated on a line of positive height. -/
theorem gamma_horizontal_integral (a b t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in a..b, (deriv Complex.Gamma ((x : ℂ) + t * I) /
      Complex.Gamma ((x : ℂ) + t * I)).re) =
      Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ := by
  let U : Set ℂ := {z | 0 < z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have havoid (z : ℂ) (hz : z ∈ U) : ∀ n : ℕ, z ≠ -n := by
    intro n h
    have hi := congrArg Complex.im h
    simp at hi
    change 0 < z.im at hz
    linarith
  have hD : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (havoid z hz)).differentiableWithinAt
  have hA := hD.analyticOnNhd hU
  have hcont : Continuous (fun x : ℝ => (deriv Complex.Gamma ((x : ℂ) + t * I) /
      Complex.Gamma ((x : ℂ) + t * I)).re) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : (x : ℂ) + t * I ∈ U := by simpa [U] using ht
    have hg := Complex.Gamma_ne_zero (havoid _ hx)
    have hq : ContinuousAt (fun z : ℂ => deriv Complex.Gamma z / Complex.Gamma z)
        ((x : ℂ) + t * I) :=
      (hA _ hx).deriv.continuousAt.div (hA _ hx).continuousAt hg
    have hline : ContinuousAt (fun x : ℝ => (x : ℂ) + t * I) x := by fun_prop
    have hcomp : ContinuousAt (fun u : ℝ => deriv Complex.Gamma ((u : ℂ) + t * I) /
        Complex.Gamma ((u : ℂ) + t * I)) x :=
      hq.comp (f := fun u : ℝ => (u : ℂ) + t * I) (x := x) hline
    exact Complex.continuous_re.continuousAt.comp hcomp
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact gamma_horizontal_log_derivative x t ht
  · exact hcont.intervalIntegrable a b

/-- Lindelof p. 81 display 8, the real derivative of the shifted logarithmic norm. -/
theorem shifted_log_norm_derivative (s : ℂ) (hs : 0 < s.im) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log ‖s + u‖) ((1 / (s + x) : ℂ).re) x := by
  have hsx : s + (x : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hlin : HasDerivAt (fun u : ℝ => s + u) (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add s
  have hlog := (hlin.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hsx))).div_const 2
  have heq : (fun u : ℝ => Real.log (‖s + u‖ ^ 2) / 2) =
      (fun u : ℝ => Real.log ‖s + u‖) := by
    ext u
    rw [Real.log_pow]
    ring
  rw [heq] at hlog
  convert hlog using 1
  rw [Complex.inner, Complex.div_re, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.one_re, Complex.one_im, Complex.conj_re,
    Complex.conj_im, one_mul, zero_mul, sub_zero]
  ring

/-- Lindelof p. 81 displays 8 and 11, finite Euler summation of the shifted real log norm.
This is the first-order source step. No Gamma representation is assumed. -/
theorem finite_log_norm_euler (s : ℂ) (hs : 0 < s.im) (N : ℕ) :
    (∑ k ∈ Finset.Ioc 0 N, Real.log ‖s + k‖) =
      (Real.log ‖s + N‖ - Real.log ‖s‖) / 2 +
        (∫ x : ℝ in (0 : ℝ)..N, Real.log ‖s + x‖) +
        ∫ x : ℝ in (0 : ℝ)..N, (1 / (s + x) : ℂ).re * B1 x := by
  have hsx (x : ℝ) : s + (x : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hderiv : deriv (fun x : ℝ => Real.log ‖s + x‖) =
      (fun x : ℝ => (1 / (s + x) : ℂ).re) := by
    ext x
    exact (shifted_log_norm_derivative s hs x).deriv
  have hc : Continuous (fun x : ℝ => (1 / (s + x) : ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.div
      (continuous_const.add Complex.continuous_ofReal) hsx)
  have h := sum_eq_integral_add_integral_deriv (f := fun x : ℝ => Real.log ‖s + x‖)
    (a := 0) (b := N) (by norm_num) (by positivity)
    (fun x hx => (shifted_log_norm_derivative s hs x).differentiableAt)
    (by rw [hderiv]; exact hc.continuousOn)
  rw [hderiv] at h
  have hB0 : B1 0 = -(1 / 2 : ℝ) := by norm_num [B1]
  have hBN : B1 (N : ℝ) = -(1 / 2 : ℝ) := by simp [B1]
  simp only [Nat.floor_zero, Nat.floor_natCast, Complex.ofReal_natCast,
    Complex.ofReal_zero, add_zero, hB0, hBN] at h
  change (∑ k ∈ Finset.Ioc 0 N, Real.log ‖s + k‖) =
    (Real.log ‖s‖ * (-(1 / 2 : ℝ)) - Real.log ‖s + N‖ * (-(1 / 2 : ℝ)) +
      (∫ x : ℝ in (0 : ℝ)..N, Real.log ‖s + x‖)) +
      ∫ x : ℝ in (0 : ℝ)..N, (1 / (s + x) : ℂ).re * B1 x at h
  convert h using 1 <;> ring

/-- Lindelof p. 97 display 3, obtained from finite Euler summation and the Gamma Euler limit. -/
lemma gamma_log_norm_stirling (s : ℂ) (hre : 0 ≤ s.re) (him : 0 < s.im) :
    Real.log ‖Complex.Gamma s‖ =
      ((s - 1 / 2) * Complex.log s - s).re + Real.log (Real.sqrt (2 * π)) +
        (s⁻¹).re / 12 - ((s⁻¹) ^ 3).re / 360 -
        (∫ x : ℝ in Ioi (0 : ℝ),
          (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4).re / 4 := by
  have havoid : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  let M := (s - 1 / 2) * Complex.log s - s
  let J := ∫ x : ℝ in Ioi (0 : ℝ),
    (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4
  have hInv := Stirling518.inv_shift_limit s him
  have hInt := intervalIntegral_tendsto_integral_Ioi 0
    (Stirling518.fourth_kernel_integrable s hre him)
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hQ := (((Stirling518.logarithmic_endpoint_limit s him).sub_const M).add
    ((hInv.sub_const s⁻¹).div_const 12)).sub
      (((hInv.pow 3).sub_const ((s⁻¹) ^ 3)).div_const 360) |>.add (hInt.div_const 4)
  have htotal := Stirling518.log_factorial_limit.sub
    (Complex.continuous_re.continuousAt.tendsto.comp hQ)
  have hlim : Tendsto (fun n : ℕ => Real.log ‖Complex.GammaSeq s n‖) atTop
      (𝓝 (Real.log (Real.sqrt (2 * π)) -
        ((0 - M) + (0 - s⁻¹) / 12 - (0 ^ 3 - (s⁻¹) ^ 3) / 360 + J / 4).re)) := by
    apply htotal.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsum : (∑ k ∈ Finset.range (n + 1), Real.log ‖s + k‖) =
        (∑ k ∈ Finset.range (n + 1), Complex.log (s + k)).re := by
      simp only [Complex.re_sum, Complex.log_re]
    rw [gamma_seq_log_norm s havoid n hn, hsum, Stirling518.finite_sum_log s him n]
    dsimp only [Function.comp_def, M]
    norm_num only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      inv_pow, one_div, mul_zero, sub_zero, zero_mul, add_zero]
    ring
  have he := tendsto_nhds_unique (gamma_log_norm_limit s havoid) hlim
  norm_num only [zero_sub, zero_pow, zero_div, Complex.add_re, Complex.sub_re,
    Complex.neg_re, Complex.zero_re, Complex.div_ofNat_re] at he
  dsimp only [M, J] at he
  linear_combination he

/-- LEAF. Backlund p. 363 display 59 and Lindelof p. 97 displays 1 and 3.
The standard Bernoulli convention retains the explicit reciprocal-cube term.
This is an identity for the real logarithmic norm of the actual Gamma function.
It does not use a principal logarithm of Gamma or an imaginary argument formula. -/
theorem real_stirling_identity (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    Real.log ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ =
      (σ - 1) / 2 * Real.log (t / 2) - π * t / 4 + Real.log (Real.sqrt (2 * π)) +
        (t / 2 * Real.arctan (σ / t) - σ / 2 +
          (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
          (stirlingRemainder (((σ : ℂ) + t * I) / 2)).re -
          (1 / (360 * (((σ : ℂ) + t * I) / 2) ^ 3)).re) := by
  let z : ℂ := ((σ : ℂ) + t * I) / 2
  have htpos : 0 < t := by linarith
  have hzre : z.re = σ / 2 := by simp [z]
  have hzim : z.im = t / 2 := by simp [z]
  have hre : 0 ≤ z.re := by rw [hzre]; exact div_nonneg hσ.1 (by norm_num)
  have him : 0 < z.im := by rw [hzim]; positivity
  have h := gamma_log_norm_stirling z hre him
  have hnorm : Real.log ‖z‖ =
      Real.log (t / 2) + Real.log (1 + (σ / t) ^ 2) / 2 := by
    have hsq : ‖z‖ ^ 2 = (t / 2) ^ 2 * (1 + (σ / t) ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
      field_simp
      ring
    have hl := congrArg Real.log hsq
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
    linarith
  have harg : z.arg = π / 2 - Real.arctan (σ / t) := by
    rw [Stirling518.arg_upper_half_plane z hre him, hzre, hzim,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hmain : ((z - 1 / 2) * Complex.log z - z).re =
      (σ - 1) / 2 * Real.log (t / 2) - π * t / 4 +
        (t / 2 * Real.arctan (σ / t) - σ / 2 +
          (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2)) := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.log_re,
      Complex.log_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
      Complex.one_im, hzre, hzim, zero_div, sub_zero, hnorm, harg]
    ring
  have hinv : (z⁻¹).re / 12 = σ / (6 * (σ ^ 2 + t ^ 2)) := by
    rw [Complex.inv_re, Complex.normSq_apply, hzre, hzim]
    field_simp
    ring
  have hcube : (1 / (360 * z ^ 3) : ℂ) = (z⁻¹) ^ 3 / 360 := by
    simp only [mul_inv, inv_pow, div_eq_mul_inv]
    ring
  have hrem : (stirlingRemainder z).re =
      -(∫ x : ℝ in Ioi (0 : ℝ),
        (bernoulliFun 4 (Int.fract x) : ℂ) / (z + x) ^ 4).re / 4 := by
    simp only [stirlingRemainder, periodicB4_eq_mathlib, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, zero_div]
    ring
  change Real.log ‖Complex.Gamma z‖ =
    (σ - 1) / 2 * Real.log (t / 2) - π * t / 4 + Real.log (Real.sqrt (2 * π)) +
      (t / 2 * Real.arctan (σ / t) - σ / 2 +
        (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
        (stirlingRemainder z).re - (1 / (360 * z ^ 3)).re)
  rw [hmain, hinv] at h
  rw [hrem, hcube, Complex.div_ofNat_re]
  linear_combination h

/-- Lindelof p. 97 display 3, uniform fourth Bernoulli polynomial bound. -/
theorem periodicB4_bound (x : ℝ) : |periodicB4 x| ≤ 1 / 30 := by
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  have hq0 : 0 ≤ Int.fract x * (1 - Int.fract x) := mul_nonneg h0 (by linarith)
  have hq1 : Int.fract x * (1 - Int.fract x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  unfold periodicB4
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (Int.fract x * (1 - Int.fract x))]
  · nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]

/-- Lindelof p. 99 display 5, the shifted fourth-power majorant integral. -/
theorem shifted_inverse_four (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => 1 / (x + y) ^ 4) (Ioi (0 : ℝ)) ∧
      (∫ x : ℝ in Ioi (0 : ℝ), 1 / (x + y) ^ 4) = 1 / (3 * y ^ 3) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / (x + y) ^ 3) / 3)
      (1 / (x + y) ^ 4) x := by
    intro x hx
    have hxy : 0 < x + y := by linarith [show 0 ≤ x from hx]
    have hn : (x + y) ^ 3 ≠ 0 := pow_ne_zero 3 hxy.ne'
    convert (((((hasDerivAt_id x).add_const y).pow 3).inv hn).neg.div_const 3) using 1
    · ext z; simp
    · simp only [Pi.pow_apply, Pi.add_apply, id_eq]
      field_simp
      <;> ring
  have ht : Tendsto (fun x : ℝ => (x + y) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ y tendsto_id)
  have hlim : Tendsto (fun x : ℝ => -(1 / (x + y) ^ 3) / 3) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, neg_zero, zero_div, Pi.inv_apply] using ht.inv_tendsto_atTop.neg.div_const 3
  have hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 1 / (x + y) ^ 4 := by intros; positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hlim, ?_⟩
  convert integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hlim using 1 <;> simp <;> ring

/-- Lindelof p. 99 display 5, the elementary sector majorant.
The real part of s is nonnegative and its imaginary part is positive. -/
theorem fourth_kernel_bound (a y x : ℝ) (ha : 0 ≤ a) (hy : 0 < y) (hx : 0 ≤ x) :
    ‖(periodicB4 x : ℂ) / (((a : ℂ) + y * I) + x) ^ 4‖ ≤
      (2 / 15 : ℝ) * (1 / (x + y) ^ 4) := by
  let z : ℂ := ((a : ℂ) + y * I) + x
  have hsq : ‖z‖ ^ 2 = (a + x) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z]
    ring
  have hzpos : 0 < ‖z‖ := by nlinarith [sq_pos_of_pos hy, norm_nonneg z]
  have hsum : 0 < x + y := by positivity
  have hquad : (x + y) ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (x - y), mul_nonneg ha hx]
  have hfour : (x + y) ^ 4 ≤ 4 * ‖z‖ ^ 4 := by
    nlinarith [sq_nonneg (2 * ‖z‖ ^ 2 - (x + y) ^ 2)]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  change |periodicB4 x| / ‖z‖ ^ 4 ≤ _
  calc |periodicB4 x| / ‖z‖ ^ 4 ≤ (1 / 30) / ‖z‖ ^ 4 :=
      div_le_div_of_nonneg_right (periodicB4_bound x) (by positivity)
    _ ≤ (2 / 15 : ℝ) * (1 / (x + y) ^ 4) := by
      rw [div_le_iff₀ (pow_pos hzpos 4)]
      have hc : (x + y) ^ 4 ≠ 0 := (pow_pos hsum 4).ne'
      field_simp
      nlinarith [hfour]

/-- Backlund p. 364, the Stieltjes step before display 60.
Derived norm estimate for the standard Bernoulli integral contribution.
The reciprocal-cube endpoint correction is bounded separately. No Gamma value occurs. -/
theorem stirling_remainder_bound (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    ‖stirlingRemainder (((σ : ℂ) + t * I) / 2)‖ ≤ 4 / (45 * t ^ 3) := by
  have htpos : 0 < t := by linarith
  have hy : 0 < t / 2 := by positivity
  have hi := (shifted_inverse_four (t / 2) hy).1.const_mul (2 / 15 : ℝ)
  have hb := norm_integral_le_of_norm_le hi (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have h := fourth_kernel_bound (σ / 2) (t / 2) x
      (by linarith [hσ.1]) hy hx.le
    convert h using 1 <;> congr 3 <;> push_cast <;> ring)
  have hint : (∫ x : ℝ in Ioi (0 : ℝ), (2 / 15 : ℝ) * (1 / (x + t / 2) ^ 4)) =
      16 / (45 * t ^ 3) := by
    rw [integral_const_mul, (shifted_inverse_four (t / 2) hy).2]
    field_simp
    <;> ring
  rw [hint] at hb
  have he (x : ℝ) : (↑(σ / 2) + ↑(t / 2) * I + ↑x : ℂ) =
      ((σ : ℂ) + t * I) / 2 + x := by push_cast; ring
  simp_rw [he] at hb
  rw [stirlingRemainder, norm_mul]
  norm_num only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 4)
  convert h using 1 <;> ring

/-- Backlund p. 364, the elementary cubic error of arctangent. -/
theorem arctan_cubic_lower (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hderiv : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
        ((1 + y ^ 2)⁻¹ - 1 + y ^ 2) y := by
    intro y hy
    convert ((Real.hasDerivAt_arctan y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 3) using 1
    · ext z; simp
    · simp
  have hmono : MonotoneOn (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3) (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact Real.continuous_arctan.sub continuous_id |>.add (continuous_id.pow 3 |>.div_const 3) |>.continuousOn
    · intro y hy
      exact (hderiv y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hderiv y (interior_subset hy)).deriv]
      have hpos : 0 < 1 + y ^ 2 := by positivity
      have hid : ((1 + y ^ 2)⁻¹ - 1 + y ^ 2) = y ^ 4 / (1 + y ^ 2) := by
        field_simp
        <;> ring
      rw [hid]
      positivity
  have h := hmono (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, hx⟩) ⟨hx, le_rfl⟩ hx
  simp only [Real.arctan_zero, sub_zero, zero_pow, zero_div, zero_add] at h
  linarith

/-- Backlund p. 364, the combined real Stirling error before exponentiation.
CONDITIONAL ON stirling_remainder_bound. The Gamma identity is not used. -/
theorem real_error_sharp (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    |t / 2 * Real.arctan (σ / t) - σ / 2 +
      (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
      (stirlingRemainder (((σ : ℂ) + t * I) / 2)).re| ≤ 9 / (20 * t ^ 2) := by
  let u := 1 / t ^ 2
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := htpos.ne'
  have hu : 0 < u := by dsimp [u]; positivity
  have hx0 : 0 ≤ σ / t := div_nonneg hσ.1 htpos.le
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have hσ3 : σ ^ 3 ≤ 1 := by nlinarith [mul_nonneg hσ.1 (sub_nonneg.mpr hσ.2)]
  have hx2 : (σ / t) ^ 2 ≤ u := by
    dsimp [u]
    rw [div_pow]
    exact div_le_div_of_nonneg_right hσ2 (sq_nonneg t)
  have hatan0 := mul_le_mul_of_nonneg_left (Real.arctan_le_self hx0) (show 0 ≤ t / 2 by positivity)
  have hatan1 := mul_le_mul_of_nonneg_left (arctan_cubic_lower (σ / t) hx0)
    (show 0 ≤ t / 2 by positivity)
  have hatanid : t / 2 * (σ / t) = σ / 2 := by field_simp
  have hcubid : t / 2 * ((σ / t) ^ 3 / 3) = σ ^ 3 * u / 6 := by
    dsimp [u]
    field_simp
    <;> ring
  have hatanlo : -u / 6 ≤ t / 2 * Real.arctan (σ / t) - σ / 2 := by
    rw [mul_sub, hatanid, hcubid] at hatan1
    nlinarith [mul_le_mul_of_nonneg_right hσ3 hu.le]
  have hatanup : t / 2 * Real.arctan (σ / t) - σ / 2 ≤ 0 := by
    rw [hatanid] at hatan0
    linarith
  have hlog0 : 0 ≤ Real.log (1 + (σ / t) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  have hlog1 : Real.log (1 + (σ / t) ^ 2) ≤ u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (σ / t) ^ 2 by positivity)
    linarith
  have hloglo : -u / 4 ≤ (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) := by
    nlinarith [mul_nonneg hσ.1 hlog0]
  have hlogup : (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hσ.2]) hlog0
  have hcorr0 : 0 ≤ σ / (6 * (σ ^ 2 + t ^ 2)) := div_nonneg hσ.1 (by positivity)
  have hcorr1 : σ / (6 * (σ ^ 2 + t ^ 2)) ≤ u / 6 := by
    dsimp [u]
    rw [div_div, div_le_div_iff₀ (by positivity : 0 < 6 * (σ ^ 2 + t ^ 2))
      (by positivity : 0 < t ^ 2 * 6)]
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hσ.2)]
  have hrem := stirling_remainder_bound σ t hσ ht
  have hrem1 : ‖stirlingRemainder (((σ : ℂ) + t * I) / 2)‖ ≤ u / 500 := by
    refine hrem.trans ?_
    dsimp [u]
    rw [div_div, div_le_div_iff₀ (by positivity : 0 < 45 * t ^ 3)
      (by positivity : 0 < t ^ 2 * 500)]
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht)]
  have hrealrem := Complex.abs_re_le_norm (stirlingRemainder (((σ : ℂ) + t * I) / 2))
  have habs := hrealrem.trans hrem1
  rw [abs_le] at habs ⊢
  have hhalf : 9 / (20 * t ^ 2) = 9 * u / 20 := by dsimp [u]; ring
  rw [hhalf]
  constructor <;> linarith [habs.1, habs.2]

/-- Backlund p. 364, the combined real Stirling error before exponentiation.
CONDITIONAL ON stirling_remainder_bound. The Gamma identity is not used. -/
theorem real_error_bound (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    |t / 2 * Real.arctan (σ / t) - σ / 2 +
      (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
      (stirlingRemainder (((σ : ℂ) + t * I) / 2)).re| ≤ 1 / (2 * t ^ 2) := by
  have h := real_error_sharp σ t hσ ht
  refine h.trans ?_
  have htpos : 0 < t := by linarith
  apply (div_le_div_iff₀ (by positivity : 0 < 20 * t ^ 2) (by positivity : 0 < 2 * t ^ 2)).mpr
  nlinarith [sq_nonneg t]

/-- Lindelof p. 97 display 3 in the standard Bernoulli convention.
The explicit reciprocal-cube correction has a height majorant. -/
theorem reciprocal_cube_bound (σ t : ℝ) (ht : 50 ≤ t) :
    ‖(1 : ℂ) / (360 * (((σ : ℂ) + t * I) / 2) ^ 3)‖ ≤ 1 / (45 * t ^ 3) := by
  let z : ℂ := ((σ : ℂ) + t * I) / 2
  have htpos : 0 < t := by linarith
  have hz : t / 2 ≤ ‖z‖ := by
    have h := Complex.im_le_norm z
    simpa [z] using h
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hc : (t / 2) ^ 3 ≤ ‖z‖ ^ 3 := pow_le_pow_left₀ (by positivity) hz 3
  rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_ofNat]
  rw [div_le_div_iff₀ (by positivity : 0 < 360 * ‖z‖ ^ 3)
    (by positivity : 0 < 45 * t ^ 3)]
  dsimp [z] at *
  nlinarith [hc]

/-- Backlund p. 364, the full real error with the standard Bernoulli correction. -/
theorem corrected_real_error_bound (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    |t / 2 * Real.arctan (σ / t) - σ / 2 +
      (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
      (stirlingRemainder (((σ : ℂ) + t * I) / 2)).re -
      (1 / (360 * (((σ : ℂ) + t * I) / 2) ^ 3)).re| ≤ 1 / (2 * t ^ 2) := by
  have hmain := real_error_sharp σ t hσ ht
  have hcor := (Complex.abs_re_le_norm ((1 : ℂ) / (360 * (((σ : ℂ) + t * I) / 2) ^ 3))).trans
    (reciprocal_cube_bound σ t ht)
  refine (abs_sub _ _).trans ((add_le_add hmain hcor).trans ?_)
  have htpos : 0 < t := by linarith
  rw [div_add_div] <;> try positivity
  rw [div_le_div_iff₀ (by positivity : 0 < 20 * t ^ 2 * (45 * t ^ 3))
    (by positivity : 0 < 2 * t ^ 2)]
  nlinarith [mul_nonneg (pow_nonneg htpos.le 4) (sub_nonneg.mpr ht)]

/-- Backlund p. 364 displays 60 and 61, exponentiating a small real error. -/
theorem exponential_relative (u e : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2500)
    (he : |e| ≤ u / 2) : 1 - u ≤ Real.exp e ∧ Real.exp e ≤ 1 + u := by
  have habs := abs_le.mp he
  constructor
  · linarith [Real.add_one_le_exp e]
  · have hmono : Real.exp e ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr habs.2
    have hb := Real.exp_bound_div_one_sub_of_interval (show 0 ≤ u / 2 by linarith)
      (show u / 2 < 1 by linarith)
    refine hmono.trans (hb.trans ?_)
    rw [div_le_iff₀ (by linarith : 0 < 1 - u / 2)]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]

/-- Backlund p. 364 displays 60 and 61, exact Gamma leaf from smaller source pieces.
CONDITIONAL ON real_stirling_identity and stirling_remainder_bound.
Neither source piece restates this norm inequality. -/
theorem gamma_relative (σ t : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : 50 ≤ t) :
    let G := Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)
    G * (1 - 1 / t ^ 2) ≤ ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ ∧
    ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ ≤ G * (1 + 1 / t ^ 2) := by
  let e := t / 2 * Real.arctan (σ / t) - σ / 2 +
    (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) + σ / (6 * (σ ^ 2 + t ^ 2)) +
    (stirlingRemainder (((σ : ℂ) + t * I) / 2)).re -
    (1 / (360 * (((σ : ℂ) + t * I) / 2) ^ 3)).re
  let G := Real.sqrt (2 * π) * (t / 2) ^ ((σ - 1) / 2) * Real.exp (-π * t / 4)
  have htpos : 0 < t := by linarith
  have hg : Complex.Gamma (((σ : ℂ) + t * I) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hGpos : 0 < G := by dsimp [G]; positivity
  have hlogG : Real.log G = (σ - 1) / 2 * Real.log (t / 2) - π * t / 4 +
      Real.log (Real.sqrt (2 * π)) := by
    dsimp [G]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    ring
  have hidentity : ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ = G * Real.exp e := by
    have h := real_stirling_identity σ t hσ ht
    change Real.log ‖Complex.Gamma (((σ : ℂ) + t * I) / 2)‖ = _ + e at h
    rw [← hlogG] at h
    have hexp := congrArg Real.exp h
    rw [Real.exp_log (norm_pos_iff.mpr hg), Real.exp_add, Real.exp_log hGpos] at hexp
    exact hexp
  have hu1 : 1 / t ^ 2 ≤ 1 / 2500 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500)
    nlinarith
  have h := exponential_relative (1 / t ^ 2) e (by positivity) hu1
    (by simpa [e, div_div, mul_comm, div_eq_mul_inv] using corrected_real_error_bound σ t hσ ht)
  change G * (1 - 1 / t ^ 2) ≤ _ ∧ _ ≤ G * (1 + 1 / t ^ 2)
  rw [hidentity]
  exact ⟨mul_le_mul_of_nonneg_left h.1 hGpos.le, mul_le_mul_of_nonneg_left h.2 hGpos.le⟩

end LeanLab.RamareSaouter2003.Decomp579c

#print axioms LeanLab.RamareSaouter2003.Decomp579c.periodicB4_bound
#print axioms LeanLab.RamareSaouter2003.Decomp579c.arctan_cubic_lower

#print axioms LeanLab.RamareSaouter2003.Decomp579c.real_stirling_identity
#print axioms LeanLab.RamareSaouter2003.Decomp579c.stirling_remainder_bound
#print axioms LeanLab.RamareSaouter2003.Decomp579c.real_error_bound
#print axioms LeanLab.RamareSaouter2003.Decomp579c.exponential_relative
#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_relative

#print axioms LeanLab.RamareSaouter2003.Decomp579c.shifted_inverse_four
#print axioms LeanLab.RamareSaouter2003.Decomp579c.fourth_kernel_bound

#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_log_norm_limit
#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_seq_log_norm

#print axioms LeanLab.RamareSaouter2003.Decomp579c.real_error_sharp
#print axioms LeanLab.RamareSaouter2003.Decomp579c.reciprocal_cube_bound
#print axioms LeanLab.RamareSaouter2003.Decomp579c.corrected_real_error_bound

#print axioms LeanLab.RamareSaouter2003.Decomp579c.periodicB4_eq_mathlib

#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_horizontal_log_derivative

#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_horizontal_integral

#print axioms LeanLab.RamareSaouter2003.Decomp579c.shifted_log_norm_derivative
#print axioms LeanLab.RamareSaouter2003.Decomp579c.finite_log_norm_euler
#print axioms LeanLab.RamareSaouter2003.Decomp579c.gamma_log_norm_stirling
