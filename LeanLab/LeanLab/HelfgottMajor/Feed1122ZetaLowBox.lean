import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Split of `noLowZero_level_one`: `ζ` has no zero in `(0,1) × (0,1]`, burst 20261122 S126

The conductor one leaf of `Feed1122VeryLowNoZero` asks that the Riemann zeta function have no
zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 1`. Helfgott, arXiv 1305.2897v4 Section 4.6 page 56,
takes it from Platt's verification [Pla11]; at this height no zero computation is needed, the
Euler Maclaurin formula with two Bernoulli terms already separates `ζ` from `0`:

`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)/2 · ∫_1^∞ B₂({u}) u^(-s-2) du`, valid for `Re s > 0`,
with `B₂(y) = y² - y + 1/6`, Edwards, Riemann's Zeta Function, 1974, Chapter 6, and
Titchmarsh, The Theory of the Riemann Zeta-Function, Section 2.1, display 2.1.5 integrated by
parts once more. The main term is `1/(s-1) + 1/2 + s/12`.

* PROVED `riemannZeta_eq_EM2`: that formula, from the first order formula `ZetaAltFormula` of the
  PNT port by one integration by parts on `[1, N]` with right derivatives, `ibp_Ioi`, and `N → ∞`.
* PROVED `norm_EM2_int_le`: `|B₂| ≤ 1/6`, so the integral is at most `1/(6(Re s + 1))`.
* PROVED `zeta_lowbox_ineq`: on the box the main term beats the remainder, a polynomial
  inequality in `Re s` and `Im s`, squared: left side below `20`, right side above `36`.
* PROVED `riemannZeta_ne_zero_lowbox`: the assembly.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaLowBox
open Complex Set MeasureTheory Filter Topology

/-- The fractional part has right derivative `1` everywhere. -/
lemma hasDerivWithinAt_fract (x : ℝ) : HasDerivWithinAt Int.fract 1 (Ioi x) x := by
  have hlt : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have hev : Int.fract =ᶠ[𝓝[>] x] fun y => y - ⌊x⌋ := by
    filter_upwards [Ico_mem_nhdsGT hlt] with y hy
    have : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      exact ⟨(Int.floor_le x).trans hy.1, hy.2⟩
    rw [Int.fract, this]
  have h1 : HasDerivWithinAt (fun y : ℝ => y - ⌊x⌋) 1 (Ioi x) x :=
    ((hasDerivAt_id x).sub_const _).hasDerivWithinAt
  exact h1.congr_of_eventuallyEq hev (by rw [Int.fract])

/-- `B₂({x})` is continuous, since `B₂(0) = B₂(1)`. -/
lemma continuous_B2fract : Continuous fun x : ℝ => (Int.fract x) ^ 2 - Int.fract x + 1 / 6 := by
  have := ContinuousOn.comp_fract'' (f := fun y : ℝ => y ^ 2 - y + 1 / 6)
    (by fun_prop) (by norm_num)
  exact this


/-- A bounded measurable real weight times `x^a`, `Re a < -1`, is integrable on `(1, ∞)`. -/
lemma integrableOn_weight_cpow {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    {a : ℂ} (ha : a.re < -1) :
    IntegrableOn (fun x : ℝ => ((g x : ℝ) : ℂ) * (x : ℂ) ^ a) (Ioi 1) := by
  have hint : IntegrableOn (fun x : ℝ => C * x ^ a.re) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  refine hint.mono' ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hg).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [mem_Ioi] at hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (by linarith) _)

/-- `|1/2 - {x}| ≤ 1/2`. -/
lemma abs_half_sub_fract_le (x : ℝ) : |1 / 2 - Int.fract x| ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> linarith

/-- `|B₂({x})| ≤ 1/6`. -/
lemma abs_B2_le (x : ℝ) : |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| ≤ 1 / 6 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> nlinarith

/-- integration by parts on `Ioi 1`: `∫ (1/2 - {x}) x^(-s-1) + (s+1)/2 ∫ B₂({x}) x^(-s-2) = 1/12`. -/
lemma ibp_Ioi {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1)) +
      (s + 1) / 2 * ∫ x in Ioi (1 : ℝ), (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 2) = 1 / 12 := by
  set B : ℝ → ℝ := fun x => (Int.fract x) ^ 2 - Int.fract x + 1 / 6 with hBdef
  set f1 : ℝ → ℂ := fun x => (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1) with hf1
  set f2 : ℝ → ℂ := fun x => ((B x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2) with hf2
  set G : ℝ → ℂ := fun x => -((B x / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) with hG
  have hmf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  have i1 : IntegrableOn f1 (Ioi 1) :=
    integrableOn_weight_cpow (measurable_const.sub hmf) abs_half_sub_fract_le
      (by simp; linarith)
  have i2 : IntegrableOn f2 (Ioi 1) :=
    integrableOn_weight_cpow (((hmf.pow_const 2).sub hmf).add_const _) abs_B2_le
      (by simp; linarith)
  have i12 : IntegrableOn (fun x => f1 x + (s + 1) / 2 * f2 x) (Ioi 1) :=
    i1.add (i2.const_mul _)
  have hr : (-s - 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  -- right derivative of G
  have hderiv : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivWithinAt G (f1 x + (s + 1) / 2 * f2 x) (Ioi x) x := by
    intro x hx
    rw [mem_Ioi] at hx
    have hfr := hasDerivWithinAt_fract x
    have hB : HasDerivWithinAt (fun y => B y / 2) ((2 * Int.fract x * 1 - 1) / 2) (Ioi x) x := by
      have := ((hfr.pow 2).sub hfr).add_const (1 / 6 : ℝ)
      simpa [hBdef] using this.div_const 2
    have hBc := hB.ofReal_comp
    have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * x ^ (-s - 1 - 1)) x :=
      hasDerivAt_ofReal_cpow_const (by linarith) hr
    have := (hBc.neg).mul hp.hasDerivWithinAt
    convert this using 1
    simp only [hf1, hf2, hBdef, Pi.neg_apply]
    have e : (-s - 1 - 1) = -s - 2 := by ring
    rw [e]
    push_cast
    ring
  have hcont : Continuous B := continuous_B2fract
  have hGcont : ∀ b : ℝ, 1 ≤ b → ContinuousOn G (Icc 1 b) := by
    intro b _
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp ((hcont.div_const 2))).neg.continuousOn
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      exact (hasDerivAt_ofReal_cpow_const hx0.ne' hr).continuousAt.continuousWithinAt
  have hfin : ∀ n : ℕ, 1 ≤ n →
      ∫ x in (1 : ℝ)..n, (f1 x + (s + 1) / 2 * f2 x) = G n - G 1 := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hn' (hGcont n hn')
    · intro x hx
      exact hderiv x hx.1
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn').mpr
        (i12.mono_set Ioc_subset_Ioi_self)
  have hGn : ∀ n : ℕ, G n = -(1 / 12) * (n : ℂ) ^ (-s - 1) := by
    intro n
    simp only [hG, hBdef, Int.fract_natCast]
    push_cast
    ring
  have hG1 : G 1 = -(1 / 12) := by
    have := hGn 1
    simpa using this
  have hlim1 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, (f1 x + (s + 1) / 2 * f2 x)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (f1 x + (s + 1) / 2 * f2 x))) :=
    intervalIntegral_tendsto_integral_Ioi 1 i12 tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℂ) ^ (-s - 1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := s.re + 1) (by linarith)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards with n
      simp only [Function.comp_apply]
      congr 1
      ring
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
    simp
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, (f1 x + (s + 1) / 2 * f2 x)) atTop
      (𝓝 (1 / 12)) := by
    have : Tendsto (fun n : ℕ => G n - G 1) atTop (𝓝 (-(1 / 12) * 0 - -(1 / 12))) := by
      simp_rw [hGn, hG1]
      exact ((hpow.const_mul _).sub_const _)
    rw [show (-(1 / 12) * 0 - -(1 / 12) : ℂ) = 1 / 12 by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hfin n hn).symm
  have hval := tendsto_nhds_unique hlim1 hlim2
  rw [integral_add i1 (i2.const_mul _), integral_const_mul] at hval
  exact hval

/-- PROVED burst S126, was LEAF MEDIUM: Euler Maclaurin formula for `ζ` with two Bernoulli terms, valid in `Re s > 0`, Edwards,
Riemann's Zeta Function, Chapter 6, and Titchmarsh Section 2.1 display 2.1.5 integrated by parts
once more: `ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)/2 ∫_1^∞ B₂({u}) u^(-s-2) du`. In the lab it
follows from `ZetaAltFormula`, `ζ = 1 + 1/(s-1) - s ∫_1^∞ {u} u^(-s-1) du`, by splitting
`{u} = 1/2 + ({u} - 1/2)` and integrating `({u} - 1/2) u^(-s-1)` by parts on each `[n, n+1]`
against `B₂({u})/2`, whose values at the integers are `1/12`. Class MEDIUM. -/
theorem riemannZeta_eq_EM2 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) / 2 *
      ∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
        (u : ℂ) ^ (-s - 2) := by
  have hI := ibp_Ioi hs
  rw [ZetaAltFormula hs h1, riemannZeta1]
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hre : (-s - 1).re < -1 := by simp; linarith
  have ipow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hre one_pos
  have i1 : IntegrableOn (fun x : ℝ => (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) :=
    integrableOn_weight_cpow (measurable_const.sub measurable_fract) abs_half_sub_fract_le hre
  have hpow : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) = 1 / s := by
    rw [integral_Ioi_cpow_of_lt hre one_pos]
    have : (-s - 1 + 1) = -s := by ring
    rw [this]
    simp
  have hsplit : ∫ u in Ioi (1 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      1 / 2 * (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1)) -
        ∫ x in Ioi (1 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← integral_const_mul, ← integral_sub (ipow.const_mul _) i1]
    congr 1
    ext x
    push_cast
    ring
  rw [hsplit, hpow]
  set J := ∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
    (u : ℂ) ^ (-s - 2)
  set I1 := ∫ x in Ioi (1 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1)
  have hI1 : I1 = 1 / 12 - (s + 1) / 2 * J := by linear_combination hI
  rw [hI1]
  field_simp
  ring

/-- The second Bernoulli polynomial is at most `1/6` in absolute value on `[0, 1)`. -/
lemma abs_bernoulli2_fract_le (x : ℝ) :
    |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| ≤ 1 / 6 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]
  constructor <;> nlinarith

/-- The remainder integral of the second order formula is at most `1/(6(Re s + 1))`, the
argument of `norm_zetaInt_le` in `PNTPort.ZetaZeros.SmallT` with `|B₂| ≤ 1/6`. -/
lemma norm_EM2_int_le {s : ℂ} (hs : -1 < s.re) :
    ‖∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
      (u : ℂ) ^ (-s - 2)‖ ≤ 1 / (6 * (s.re + 1)) := by
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) :
      |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| * ‖(x : ℂ) ^ (-s - 2)‖
        ≤ 1 / 6 * x ^ (-s.re - 2) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [sub_re, neg_re, ofReal_ofNat, re_ofNat]
    exact mul_le_mul_of_nonneg_right (abs_bernoulli2_fract_le x)
      (Real.rpow_nonneg (by linarith) _)
  have domIntegral : Integrable (fun x : ℝ => 1 / 6 * x ^ (-s.re - 2))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) one_pos
  have hval : ∫ x in Ioi (1 : ℝ), 1 / 6 * x ^ (-s.re - 2) = 1 / (6 * (s.re + 1)) := by
    rw [integral_const_mul, hI, Real.one_rpow]
    have : -s.re - 2 + 1 = -(s.re + 1) := by ring
    rw [this]
    have hp : s.re + 1 ≠ 0 := by linarith
    field_simp
  rw [← hval]
  refine integral_mono_ae ?_ domIntegral ?_
  · refine domIntegral.mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp
        (((measurable_fract.pow_const 2).sub measurable_fract).add_const _)).mul
        (Complex.measurable_ofReal.pow_const _)).norm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact domBound hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact domBound hx

/-- On the box `0 < Re s < 1`, `0 < Im s ≤ 1` the main term of the second order formula beats
the remainder bound. Squared: `|s|² |s+1|² |s-1|² < 2 · 5 · 2 = 20` and
`(Re s + 1)² |s+2|² |s+3|² > 1 · 4 · 9 = 36`. -/
lemma zeta_lowbox_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 0 < s.im)
    (ht1 : s.im ≤ 1) :
    ‖s‖ * ‖s + 1‖ / (12 * (s.re + 1)) < ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ := by
  set σ := s.re
  set t := s.im
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have a1 : ‖s‖ ^ 2 < 2 := by rw [hsq]; nlinarith
  have a2 : ‖s + 1‖ ^ 2 < 5 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have a3 : ‖s - 1‖ ^ 2 < 2 := by
    rw [hsq]; simp only [sub_re, one_re, sub_im, one_im]; nlinarith
  have b2 : 4 < ‖s + 2‖ ^ 2 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have b3 : 9 < ‖s + 3‖ ^ 2 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hn1 : 0 < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hA : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s - 1‖ := by positivity
  have hkey : ‖s‖ * ‖s + 1‖ * ‖s - 1‖ < (σ + 1) * (‖s + 2‖ * ‖s + 3‖) := by
    have hB : 0 ≤ (σ + 1) * (‖s + 2‖ * ‖s + 3‖) := by positivity
    have lhs : (‖s‖ * ‖s + 1‖ * ‖s - 1‖) ^ 2 < 20 := by
      have e : (‖s‖ * ‖s + 1‖ * ‖s - 1‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s - 1‖ ^ 2 := by ring
      rw [e]
      have p1 : 0 ≤ ‖s‖ ^ 2 := by positivity
      have p2 : 0 ≤ ‖s + 1‖ ^ 2 := by positivity
      have p3 : 0 ≤ ‖s - 1‖ ^ 2 := by positivity
      have q1 : ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 < 2 * 5 := mul_lt_mul'' a1 a2 p1 p2
      have q2 := mul_lt_mul'' q1 a3 (by positivity) p3
      linarith
    have rhs : 36 < ((σ + 1) * (‖s + 2‖ * ‖s + 3‖)) ^ 2 := by
      have e : ((σ + 1) * (‖s + 2‖ * ‖s + 3‖)) ^ 2 =
          (σ + 1) ^ 2 * (‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2) := by ring
      rw [e]
      have c1 : 1 < (σ + 1) ^ 2 := by nlinarith
      have c2 : 36 < ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 := by nlinarith
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hB (by linarith)
  rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `ζ` has no zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 1`: the second order Euler Maclaurin
formula, the remainder bound, and the box inequality. -/
theorem riemannZeta_ne_zero_lowbox (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (ht0 : 0 < ρ.im)
    (ht1 : ρ.im ≤ 1) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hEM := riemannZeta_eq_EM2 h0 hρ1
  set I := ∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
    (u : ℂ) ^ (-ρ - 2) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) = ρ * (ρ + 1) / 2 * I := by
    rw [hz] at hEM
    linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / (6 * (ρ.re + 1)) := norm_EM2_int_le (by linarith)
  have hlt := zeta_lowbox_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have e : ‖ρ‖ * ‖ρ + 1‖ / 2 * (1 / (6 * (ρ.re + 1))) = ‖ρ‖ * ‖ρ + 1‖ / (12 * (ρ.re + 1)) := by
    field_simp
    ring
  linarith

end LeanLab.HelfgottMajor.Feed1122ZetaLowBox
