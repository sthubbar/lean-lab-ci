import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Split of `card1_zeta_zero_free_below_fourteen` at height `4`, burst 20261122 S126

The leaf asks that `ζ` have no zero in the open strip with ordinate in `(1, 14]`, the classical
fact that the first zero is at `14.1347…`. Below height `4` no zero computation is needed: the
Euler Maclaurin formula with two Bernoulli terms,
`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)(s+2)/720 - s(s+1)(s+2)(s+3)/24 ∫_1^∞ B₄({u}) u^(-s-4) du`,
valid in `Re s > 0`, Edwards, Riemann's Zeta Function, 1974, Chapter 6, separates `ζ` from `0`.

* PROVED `riemannZeta_eq_EM4`: that formula, from the lab `ZetaAltFormula` by three integrations
  by parts on `(1, ∞)`, each by the right derivative FTC on `[1, N]` and `N → ∞`, `ibp_gen`.
* PROVED `norm_weight_int_le`: the remainder integral is at most `1/(360(Re s + 3))`.
* PROVED `zeta_box_one_four_ineq`: the main term beats that bound on `(0,1) × (1,4]`.
* LEAF HARD `zeta_zero_free_four_fourteen`: no zero with ordinate in `(4, 14]`.
* PROVED assembly `card1_zeta_zero_free_below_fourteen_split`, exactly the leaf's statement.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaEM4
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


/-- generic integration by parts on `Ioi 1` against a continuous weight `P` with right
derivative `p`, constant `P0` at the integers. -/
lemma ibp_gen {P p : ℝ → ℝ} (hPc : Continuous P) (hPd : ∀ x, HasDerivWithinAt P (p x) (Ioi x) x)
    (hPm : Measurable P) (hpm : Measurable p) {C C' : ℝ} (hPb : ∀ x, |P x| ≤ C)
    (hpb : ∀ x, |p x| ≤ C') {P0 : ℝ} (hP0 : ∀ n : ℕ, P n = P0) {a : ℂ} (ha : a.re < -1) :
    (∫ x in Ioi (1 : ℝ), ((p x : ℝ) : ℂ) * (x : ℂ) ^ a) +
      a * ∫ x in Ioi (1 : ℝ), ((P x : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) = -(P0 : ℂ) := by
  set f1 : ℝ → ℂ := fun x => ((p x : ℝ) : ℂ) * (x : ℂ) ^ a with hf1
  set f2 : ℝ → ℂ := fun x => ((P x : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) with hf2
  set G : ℝ → ℂ := fun x => ((P x : ℝ) : ℂ) * (x : ℂ) ^ a with hG
  have i1 : IntegrableOn f1 (Ioi 1) := integrableOn_weight_cpow hpm hpb ha
  have i2 : IntegrableOn f2 (Ioi 1) := integrableOn_weight_cpow hPm hPb (by simp; linarith)
  have i12 : IntegrableOn (fun x => f1 x + a * f2 x) (Ioi 1) := i1.add (i2.const_mul _)
  have hr : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; linarith
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt G (f1 x + a * f2 x) (Ioi x) x := by
    intro x hx
    rw [mem_Ioi] at hx
    have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ a) (a * x ^ (a - 1)) x :=
      hasDerivAt_ofReal_cpow_const (by linarith) hr
    have := (hPd x).ofReal_comp.mul hp.hasDerivWithinAt
    convert this using 1
    simp only [hf1, hf2]
    ring
  have hGcont : ∀ b : ℝ, ContinuousOn G (Icc 1 b) := by
    intro b
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp hPc).continuousOn ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    exact (hasDerivAt_ofReal_cpow_const hx0.ne' hr).continuousAt.continuousWithinAt
  have hfin : ∀ n : ℕ, 1 ≤ n → ∫ x in (1 : ℝ)..n, (f1 x + a * f2 x) = G n - G 1 := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hn' (hGcont n)
    · intro x hx
      exact hderiv x hx.1
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn').mpr
        (i12.mono_set Ioc_subset_Ioi_self)
  have hGn : ∀ n : ℕ, G n = (P0 : ℂ) * (n : ℂ) ^ a := by
    intro n
    simp only [hG, hP0]
    rfl
  have hG1 : G 1 = (P0 : ℂ) := by
    have := hGn 1
    simpa using this
  have hlim1 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, (f1 x + a * f2 x)) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), (f1 x + a * f2 x))) :=
    intervalIntegral_tendsto_integral_Ioi 1 i12 tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℂ) ^ a) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ a.re) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := -a.re) (by linarith)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards with n
      simp only [Function.comp_apply, neg_neg]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, (f1 x + a * f2 x)) atTop
      (𝓝 (-(P0 : ℂ))) := by
    have : Tendsto (fun n : ℕ => G n - G 1) atTop (𝓝 ((P0 : ℂ) * 0 - P0)) := by
      simp_rw [hGn, hG1]
      exact ((hpow.const_mul _).sub_const _)
    rw [show ((P0 : ℂ) * 0 - P0) = -(P0 : ℂ) by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hfin n hn).symm
  have hval := tendsto_nhds_unique hlim1 hlim2
  rw [integral_add i1 (i2.const_mul _), integral_const_mul] at hval
  exact hval

/-- Integration by parts on `Ioi 1`, first step: `∫ (1/2 - {x}) x^(-s-1) + (s+1)/2 ∫ B₂({x}) x^(-s-2) = 1/12`. -/
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

/-- Euler Maclaurin with one Bernoulli term, `ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)/2 ∫ B₂({u}) u^(-s-2)`, from the lab `ZetaAltFormula`. -/
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


/-- `|B₃({x})/3| ≤ 1`, a crude bound. -/
lemma abs_B3_le (x : ℝ) : |((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 + 1 / 2 * Int.fract x) / 3| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- `|B₄({x})/12| ≤ 1/360`, since `B₄(y) = y²(1-y)² - 1/30`. -/
lemma abs_B4_le (x : ℝ) :
    |((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12| ≤ 1 / 360 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have e : (Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 =
      (Int.fract x * (1 - Int.fract x)) ^ 2 := by ring
  have hy : 0 ≤ Int.fract x * (1 - Int.fract x) := mul_nonneg h0 (by linarith)
  have hy' : Int.fract x * (1 - Int.fract x) ≤ 1 / 4 := by nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  rw [abs_le]; constructor <;> nlinarith

/-- `|B₃({x})|/3 ≤ 1`. -/
lemma abs_B3d_le (x : ℝ) : |(Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 + 1 / 2 * Int.fract x| / 3 ≤ 1 := by
  have := abs_B3_le x
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)] at this
  exact this

/-- step three: `∫ B₂ x^(-s-2) = (s+2) ∫ (B₃/3) x^(-s-3)`. -/
lemma ibp3 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2)) =
      (s + 2) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 +
        1 / 2 * Int.fract x) / 3 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have hmf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  have hc : Continuous fun x : ℝ =>
      ((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 + 1 / 2 * Int.fract x) / 3 := by
    have := ContinuousOn.comp_fract'' (f := fun y : ℝ => (y ^ 3 - 3 / 2 * y ^ 2 + 1 / 2 * y) / 3)
      (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ =>
      ((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 + 1 / 2 * Int.fract x) / 3)
      ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((hf.pow 3).sub ((hf.pow 2).const_mul (3 / 2))).add (hf.const_mul (1 / 2)))).div_const 3
    convert this using 1
    simp
    ring
  have h := ibp_gen hc hd (by fun_prop) (((hmf.pow_const 2).sub hmf).add_const _)
    abs_B3_le abs_B2_le (P0 := 0) (by intro n; simp) (a := -s - 2) (by simp; linarith)
  have e : (-s - 2 - 1) = -s - 3 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step four: `∫ (B₃/3) x^(-s-3) = 1/360 + (s+3) ∫ (B₄/12) x^(-s-4)`. -/
lemma ibp4 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 +
        1 / 2 * Int.fract x) / 3 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3)) =
      1 / 360 + (s + 3) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 +
        (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 4) := by
  have hmf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  have hc : Continuous fun x : ℝ =>
      ((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 := by
    have := ContinuousOn.comp_fract''
      (f := fun y : ℝ => (y ^ 4 - 2 * y ^ 3 + y ^ 2 - 1 / 30) / 12) (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ =>
      ((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12)
      (((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 + 1 / 2 * Int.fract x) / 3) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((hf.pow 4).sub ((hf.pow 3).const_mul 2)).add (hf.pow 2)).sub_const
      (1 / 30 : ℝ)).div_const 12
    convert this using 1
    simp
    ring
  have h := ibp_gen hc hd (by fun_prop) (by fun_prop) abs_B4_le abs_B3_le
    (P0 := -1 / 360) (by intro n; simp; norm_num) (a := -s - 3) (by simp; linarith)
  have e : (-s - 3 - 1) = -s - 4 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- second order Euler Maclaurin: `ζ(s) = M₂(s) - s(s+1)(s+2)/720 - s(s+1)(s+2)(s+3)/2 · ∫ (B₄({u})/12) u^(-s-4)`. -/
theorem riemannZeta_eq_EM4 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 -
      s * (s + 1) * (s + 2) * (s + 3) / 2 * ∫ x in Ioi (1 : ℝ),
        ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) *
          (x : ℂ) ^ (-s - 4) := by
  rw [riemannZeta_eq_EM2 hs h1, ibp3 hs, ibp4 hs]
  ring

/-- a bounded real weight against `x^a` on `Ioi 1`: `‖∫‖ ≤ C / (-Re a - 1)`. -/
lemma norm_weight_int_le {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    {a : ℂ} (ha : a.re < -1) :
    ‖∫ x in Ioi (1 : ℝ), ((g x : ℝ) : ℂ) * (x : ℂ) ^ a‖ ≤ C / (-a.re - 1) := by
  have hint : IntegrableOn (fun x : ℝ => C * x ^ a.re) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul C
  refine (norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt ha one_pos
  have hval : ∫ x in Ioi (1 : ℝ), C * x ^ a.re = C / (-a.re - 1) := by
    rw [integral_const_mul, hI, Real.one_rpow]
    have hp : a.re + 1 ≠ 0 := by linarith
    have hq : -a.re - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval]
  refine integral_mono_ae ?_ hint ?_
  · exact (integrableOn_weight_cpow hg hC ha).norm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [mem_Ioi] at hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (by linarith) _)

/-- PROVED burst S126, was LEAF MEDIUM: the box inequality for the Euler Maclaurin formula
with two Bernoulli terms on `0 < Re s < 1`, `1 < Im s ≤ 4`. Crude bounds suffice: the remainder
is below `522/2160`, the cubic term below `93/720`, and the rational term at least `3/8`, since
`(t² + 4)(t² + 9) - (81/4)(1 + t²) = t⁴ - (29/4) t² + 63/4 > 0`. -/
lemma zeta_box_one_four_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 1 < s.im)
    (ht1 : s.im ≤ 4) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / (720 * (s.re + 3)) <
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720‖ := by
  set σ := s.re with hσ
  set t := s.im with ht
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have n0 : ‖s‖ ^ 2 ≤ 17 := by rw [hsq]; nlinarith
  have n1 : ‖s + 1‖ ^ 2 ≤ 20 := by rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have n2 : ‖s + 2‖ ^ 2 ≤ 25 := by rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n3 : ‖s + 3‖ ^ 2 ≤ 32 := by rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have p0 : 0 ≤ ‖s‖ := norm_nonneg _
  have p1 : 0 ≤ ‖s + 1‖ := norm_nonneg _
  have p2 : 0 ≤ ‖s + 2‖ := norm_nonneg _
  have p3 : 0 ≤ ‖s + 3‖ := norm_nonneg _
  -- remainder side
  have hP : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ < 522 := by
    have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 ≤ 17 * 20 * 25 * 32 := by
      have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 =
          ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 := by ring
      rw [e]
      have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
      have q2 := mul_le_mul q1 n2 (by positivity) (by norm_num)
      exact mul_le_mul q2 n3 (by positivity) (by norm_num)
    have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 < 522 ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  have hE : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / (720 * (σ + 3)) < 522 / 2160 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ := by positivity
    nlinarith
  -- cubic term
  have hB : ‖s * (s + 1) * (s + 2) / 720‖ < 93 / 720 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖) ^ 2 ≤ 17 * 20 * 25 := by
      have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 := by ring
      rw [e]
      have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
      exact mul_le_mul q1 n2 (by positivity) (by norm_num)
    have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖) ^ 2 < 93 ^ 2 := by linarith
    have h93 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
    rw [div_lt_div_iff_of_pos_right (by norm_num)]
    exact h93
  -- main rational term
  have hn1 : 0 < ‖s - 1‖ := by
    rw [norm_pos_iff]; intro h
    have := congrArg Complex.im h; simp at this; linarith
  have hA : 3 / 8 ≤ ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, le_div_iff₀ (by positivity)]
    have key : (9 / 2 * ‖s - 1‖) ^ 2 ≤ (‖s + 2‖ * ‖s + 3‖) ^ 2 := by
      have e1 : (‖s + 2‖ * ‖s + 3‖) ^ 2 = ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 := by ring
      rw [e1, mul_pow, hsq (s - 1), hsq (s + 2), hsq (s + 3)]
      simp only [add_re, add_im, sub_re, sub_im, re_ofNat, im_ofNat, one_re, one_im]
      nlinarith [sq_nonneg (t ^ 2 - 29 / 8), mul_pos h0 h0, sq_nonneg t, mul_pos h0 (by positivity : (0:ℝ) < t ^ 2)]
    have h2 : 9 / 2 * ‖s - 1‖ ≤ ‖s + 2‖ * ‖s + 3‖ :=
      le_of_pow_le_pow_left₀ two_ne_zero (by positivity) key
    linarith
  have htri := norm_sub_norm_le ((s + 2) * (s + 3) / (12 * (s - 1))) (s * (s + 1) * (s + 2) / 720)
  linarith

/-- `ζ` has no zero with `0 < Re ρ < 1` and `1 < Im ρ ≤ 4`, from the second order formula, the remainder bound `‖∫‖ ≤ 1/(360(Re ρ + 3))` and the box inequality. -/
theorem riemannZeta_ne_zero_one_four (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (ht0 : 1 < ρ.im)
    (ht1 : ρ.im ≤ 4) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM4 h0 hρ1
  set I := ∫ x in Ioi (1 : ℝ),
    ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) *
      (x : ℂ) ^ (-ρ - 4) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) - ρ * (ρ + 1) * (ρ + 2) / 720 =
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) / 2 * I := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 360 / (-(-ρ - 4).re - 1) :=
    norm_weight_int_le (by fun_prop) abs_B4_le (by simp; linarith)
  have hre : (-(-ρ - 4).re - 1) = ρ.re + 3 := by simp; ring
  rw [hre] at hIle
  have hlt := zeta_box_one_four_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have hσ : 0 < ρ.re + 3 := by linarith
  have e : ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / 2 * (1 / 360 / (ρ.re + 3)) =
      ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / (720 * (ρ.re + 3)) := by
    field_simp
    ring
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914: no zero of `ζ` in the open strip has
ordinate in `(4, 14]`; the first ordinate is `14.1347…`. Class HARD: a certified zero free
rectangle, many term Euler Maclaurin with certified enclosures of `Σ n^(-s)`. -/
theorem zeta_zero_free_four_fourteen (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 4 < ρ.im) : 14 < ρ.im := by
  sorry

/-- `card1_zeta_zero_free_below_fourteen`, exactly its statement, from the proved range
`(1, 4]` and the HARD leaf on `(4, 14]`. -/
theorem card1_zeta_zero_free_below_fourteen_split (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him1 : 1 < ρ.im) : 14 < ρ.im := by
  by_cases h4 : ρ.im ≤ 4
  · exact absurd h0 (riemannZeta_ne_zero_one_four ρ hre0 hre1 him1 h4)
  · exact zeta_zero_free_four_fourteen ρ h0 hre0 hre1 (not_le.mp h4)

end LeanLab.HelfgottMajor.Feed1122ZetaEM4
