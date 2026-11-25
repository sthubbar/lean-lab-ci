import LeanLab.HelfgottMajor.Feed1122ZetaEight

/-!
# Split of `zeta_zero_free_eight_ten_half` at height `17/2`, burst 20261122 S137

`Feed1122ZetaEight` leaves the MEDIUM LEAF `zeta_zero_free_eight_ten_half`: no zero of `ζ` in the
open strip has ordinate in `(8, 21/2]`, Helfgott arXiv 1305.2897v4 Section 4.6 page 56 with
Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

Above height `8` the Euler Maclaurin formula from `n = 1` fails, so this file starts it at `n = 2`,
Edwards, Riemann's Zeta Function, 1974, Chapter 6:
`ζ(s) = 1 + 2^(-s) H(s) - s(s+1)(s+2)(s+3)/2 ∫_2^∞ (B₄({u})/12) u^(-s-4) du`, with
`H(s) = 1/2 + 2/(s-1) + s/24 - s(s+1)(s+2)/5760`. At a zero `2^(-s) H(s)` equals the remainder
minus `1`, and `|2^(-s)| = 2^(-σ)` carries no phase, so `|H(s)| ≥ 2^σ - E ≥ 1 + 2σ/3 - E`.

* PROVED `ibp_gen2`, integration by parts on `(2, ∞)`, from `Feed1122ZetaEM4.ibp_gen`.
* PROVED `riemannZeta_eq_alt2`, the alternate formula at `N = 2`, from the lab lemma
  `Zeta0EqZeta` of `PNTPort/StrongPNT/ZetaBounds.lean`.
* PROVED `ibp1_two`, `ibp2_two`, `ibp3_two`, `riemannZeta_eq_EM4_two`, `norm_weight_int_le2`.
* PROVED `two_rpow_ge`, `coeff_two_pos`, `box_two_poly`, `main_two_lt`, `prod_two_le`.
* PROVED `riemannZeta_ne_zero_eight_seventeen_half`: no zero with ordinate in `(8, 17/2]`.
* LEAF MEDIUM `zeta_zero_free_seventeen_half_ten_half`: no zero with ordinate in `(17/2, 21/2]`.
* PROVED assembly `zeta_zero_free_eight_ten_half_s137`, exactly the statement of
  `Feed1122ZetaEight.zeta_zero_free_eight_ten_half`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo
open Complex Set MeasureTheory Filter Topology LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-- A bounded measurable real weight times `x^a`, `Re a < -1`, is integrable on `(2, ∞)`. -/
lemma integrableOn_weight_cpow2 {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    {a : ℂ} (ha : a.re < -1) :
    IntegrableOn (fun x : ℝ => ((g x : ℝ) : ℂ) * (x : ℂ) ^ a) (Ioi 2) :=
  (integrableOn_weight_cpow hg hC ha).mono_set (Ioi_subset_Ioi one_le_two)

/-- generic integration by parts on `Ioi 2`, the base 2 copy of `ibp_gen`. -/
lemma ibp_gen2 {P p : ℝ → ℝ} (hPc : Continuous P) (hPd : ∀ x, HasDerivWithinAt P (p x) (Ioi x) x)
    (hPm : Measurable P) (hpm : Measurable p) {C C' : ℝ} (hPb : ∀ x, |P x| ≤ C)
    (hpb : ∀ x, |p x| ≤ C') {P0 : ℝ} (hP0 : ∀ n : ℕ, P n = P0) {a : ℂ} (ha : a.re < -1) :
    (∫ x in Ioi (2 : ℝ), ((p x : ℝ) : ℂ) * (x : ℂ) ^ a) +
      a * ∫ x in Ioi (2 : ℝ), ((P x : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) = -((P0 : ℂ) * (2 : ℂ) ^ a) := by
  set f1 : ℝ → ℂ := fun x => ((p x : ℝ) : ℂ) * (x : ℂ) ^ a with hf1
  set f2 : ℝ → ℂ := fun x => ((P x : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) with hf2
  set G : ℝ → ℂ := fun x => ((P x : ℝ) : ℂ) * (x : ℂ) ^ a with hG
  have i1 : IntegrableOn f1 (Ioi 2) := integrableOn_weight_cpow2 hpm hpb ha
  have i2 : IntegrableOn f2 (Ioi 2) := integrableOn_weight_cpow2 hPm hPb (by simp; linarith)
  have i12 : IntegrableOn (fun x => f1 x + a * f2 x) (Ioi 2) := i1.add (i2.const_mul _)
  have hr : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; linarith
  have hderiv : ∀ x ∈ Ioi (2 : ℝ), HasDerivWithinAt G (f1 x + a * f2 x) (Ioi x) x := by
    intro x hx
    rw [mem_Ioi] at hx
    have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ a) (a * x ^ (a - 1)) x :=
      hasDerivAt_ofReal_cpow_const (by linarith) hr
    have := (hPd x).ofReal_comp.mul hp.hasDerivWithinAt
    convert this using 1
    simp only [hf1, hf2]
    ring
  have hGcont : ∀ b : ℝ, ContinuousOn G (Icc 2 b) := by
    intro b
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp hPc).continuousOn ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le two_pos hx.1
    exact (hasDerivAt_ofReal_cpow_const hx0.ne' hr).continuousAt.continuousWithinAt
  have hfin : ∀ n : ℕ, 2 ≤ n → ∫ x in (2 : ℝ)..n, (f1 x + a * f2 x) = G n - G 2 := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hn' (hGcont n)
    · intro x hx
      exact hderiv x hx.1
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hn').mpr
        (i12.mono_set Ioc_subset_Ioi_self)
  have hGn : ∀ n : ℕ, G n = (P0 : ℂ) * (n : ℂ) ^ a := by
    intro n
    simp only [hG, hP0]
    rfl
  have hG1 : G 2 = (P0 : ℂ) * (2 : ℂ) ^ a := by
    have := hGn 2
    simpa using this
  have hlim1 : Tendsto (fun n : ℕ => ∫ x in (2 : ℝ)..n, (f1 x + a * f2 x)) atTop
      (𝓝 (∫ x in Ioi (2 : ℝ), (f1 x + a * f2 x))) :=
    intervalIntegral_tendsto_integral_Ioi 2 i12 tendsto_natCast_atTop_atTop
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
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in (2 : ℝ)..n, (f1 x + a * f2 x)) atTop
      (𝓝 (-((P0 : ℂ) * (2 : ℂ) ^ a))) := by
    have : Tendsto (fun n : ℕ => G n - G 2) atTop (𝓝 ((P0 : ℂ) * 0 - P0 * (2 : ℂ) ^ a)) := by
      simp_rw [hGn, hG1]
      exact ((hpow.const_mul _).sub_const _)
    rw [show ((P0 : ℂ) * 0 - P0 * (2 : ℂ) ^ a) = -((P0 : ℂ) * (2 : ℂ) ^ a) by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (hfin n hn).symm
  have hval := tendsto_nhds_unique hlim1 hlim2
  rw [integral_add i1 (i2.const_mul _), integral_const_mul] at hval
  exact hval


/-- The alternate formula at `N = 2`, from `Zeta0EqZeta`. -/
theorem riemannZeta_eq_alt2 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) / 2 + 2 * (2 : ℂ) ^ (-s) / (s - 1) +
      s * ∫ x in Ioi (2 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  rw [← Zeta0EqZeta (N := 2) two_pos hs h1]
  unfold riemannZeta0
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hint : ∫ x in Ioi (2 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) =
      ∫ x in Ioi (2 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    simp only
    rw [show (-s - 1) = -(s + 1) by ring, Complex.cpow_neg, Int.fract]
    push_cast
    ring
  simp only [Nat.cast_ofNat]
  rw [hint]
  have e3 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num)]
    simp
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    intro h; apply h1; linear_combination -h
  have hs1' : s - 1 ≠ 0 := by
    intro h; apply h1; linear_combination h
  simp [Finset.sum_range_succ, Complex.zero_cpow hs0, e3, Complex.cpow_neg]
  field_simp
  ring

/-- `|B₂({x})/2| ≤ 1/12`. -/
lemma abs_B2_half_le (x : ℝ) : |((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2| ≤ 1 / 12 := by
  have := abs_B2_le x
  rw [abs_div, abs_two]; linarith

/-- `|{x} - 1/2| ≤ 1/2`. -/
lemma abs_fract_sub_half_le (x : ℝ) : |Int.fract x - 1 / 2| ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> linarith

/-- step one on `(2, ∞)`. -/
lemma ibp1_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
      (-s - 1) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 2) = -((1 / 12 : ℂ) * (2 : ℂ) ^ (-s - 1)) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 :=
    continuous_B2fract.div_const 2
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2)
      (Int.fract x - 1 / 2) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := (((hf.pow 2).sub hf).add_const (1 / 6 : ℝ)).div_const 2
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B2_half_le abs_fract_sub_half_le
    (P0 := 1 / 12) (by intro n; simp; norm_num) (a := -s - 1) (by simp; linarith)
  have e : (-s - 1 - 1) = -s - 2 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step two on `(2, ∞)`. -/
lemma ibp2_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2)) +
      (-s - 2) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 +
        1 / 2 * Int.fract x) / 3 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3) = 0 := by
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
  have h := ibp_gen2 hc hd (by fun_prop) (((hmf.pow_const 2).sub hmf).add_const _)
    abs_B3_le abs_B2_le (P0 := 0) (by intro n; simp) (a := -s - 2) (by simp; linarith)
  have e : (-s - 2 - 1) = -s - 3 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step three on `(2, ∞)`. -/
lemma ibp3_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 3 - 3 / 2 * (Int.fract x) ^ 2 +
        1 / 2 * Int.fract x) / 3 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3)) +
      (-s - 3) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 +
        (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 4) =
      (1 / 360 : ℂ) * (2 : ℂ) ^ (-s - 3) := by
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
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B4_le abs_B3_le
    (P0 := -1 / 360) (by intro n; simp; norm_num) (a := -s - 3) (by simp; linarith)
  have e : (-s - 3 - 1) = -s - 4 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- Euler Maclaurin from `n = 2` with two Bernoulli terms, Edwards 1974 Chapter 6:
`ζ(s) = 1 + 2^(-s) H(s) - s(s+1)(s+2)(s+3)/2 ∫_2^∞ (B₄({u})/12) u^(-s-4) du`. -/
theorem riemannZeta_eq_EM4_two {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) * (1 / 2 + 2 / (s - 1) + s / 24 -
        s * (s + 1) * (s + 2) / 5760) -
      s * (s + 1) * (s + 2) * (s + 3) / 2 * ∫ x in Ioi (2 : ℝ),
        ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) *
          (x : ℂ) ^ (-s - 4) := by
  have hA := riemannZeta_eq_alt2 hs h1
  have h1' := ibp1_two hs
  have h2' := ibp2_two hs
  have h3' := ibp3_two hs
  have c1 : (∫ x in Ioi (2 : ℝ), (((1 / 2 - Int.fract x : ℝ)) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      -∫ x in Ioi (2 : ℝ), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← integral_neg]
    congr 1
    funext x
    push_cast
    ring
  have c2 : (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 2 - Int.fract x + 1 / 6) / 2 : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 2)) =
      (1 / 2 : ℂ) * ∫ x in Ioi (2 : ℝ), (((Int.fract x) ^ 2 - Int.fract x + 1 / 6 : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 2) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    push_cast
    ring
  have p1 : (2 : ℂ) ^ (-s - 1) = (2 : ℂ) ^ (-s) / 2 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_neg_one]
    ring
  have p3 : (2 : ℂ) ^ (-s - 3) = (2 : ℂ) ^ (-s) / 8 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ (-(3 : ℂ)) = 1 / 8 := by
      rw [Complex.cpow_neg]
      norm_num
    rw [this]
    ring
  rw [c2, p1] at h1'
  rw [p3] at h3'
  rw [hA, c1]
  have hs1 : s - 1 ≠ 0 := by
    intro h; apply h1; linear_combination h
  linear_combination (-s) * h1' + (-s * (s + 1) / 2) * h2' + (-s * (s + 1) * (s + 2) / 2) * h3'

/-- a bounded real weight against `x^a` on `Ioi 2`: `‖∫‖ ≤ C 2^(Re a + 1) / (-Re a - 1)`. -/
lemma norm_weight_int_le2 {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    {a : ℂ} (ha : a.re < -1) :
    ‖∫ x in Ioi (2 : ℝ), ((g x : ℝ) : ℂ) * (x : ℂ) ^ a‖ ≤
      C * (2 : ℝ) ^ (a.re + 1) / (-a.re - 1) := by
  have hint : IntegrableOn (fun x : ℝ => C * x ^ a.re) (Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt ha two_pos).const_mul C
  refine (norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt ha (two_pos : (0 : ℝ) < 2)
  have hval : ∫ x in Ioi (2 : ℝ), C * x ^ a.re = C * (2 : ℝ) ^ (a.re + 1) / (-a.re - 1) := by
    rw [integral_const_mul, hI]
    have hp : a.re + 1 ≠ 0 := by linarith
    have hq : -a.re - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval]
  refine integral_mono_ae ?_ hint ?_
  · exact (integrableOn_weight_cpow2 hg hC ha).norm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [mem_Ioi] at hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (by linarith) _)

/-- `2^σ ≥ 1 + 2σ/3` for `σ ≥ 0`, from `exp x ≥ 1 + x` and `log 2 > 0.69`. -/
lemma two_rpow_ge (σ : ℝ) (h0 : 0 ≤ σ) : 1 + 2 * σ / 3 ≤ (2 : ℝ) ^ σ := by
  rw [Real.rpow_def_of_pos two_pos]
  have h := Real.add_one_le_exp (Real.log 2 * σ)
  have hl := Real.log_two_gt_d9
  nlinarith

/-- The coefficient certificate on `[64, 289/4]`, proved monomial by monomial. -/
lemma coeff_two_pos (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : 64 ≤ x) (hb : x ≤ 289 / 4) :
    0 < (-x ^ 4 - 486 * x ^ 3 - 51369 * x ^ 2 + (258812636 / 25) * x - (1537035264 / 25)) +
      (-4 * x ^ 3 - 14888 * x ^ 2 + 26492060 * x - (1103023872 / 25)) * g +
      (-4 * x ^ 3 - 494 * x ^ 2 + 14525758 * x - (974230564 / 25)) * g ^ 2 +
      (-12 * x ^ 2 - 8640 * x - 2860900) * g ^ 3 +
      (-6 * x ^ 2 + 470 * x + 14715367) * g ^ 4 +
      (-12 * x + 6248) * g ^ 5 +
      (-4 * x + 478) * g ^ 6 +
      (-4) * g ^ 7 +
      (-1) * g ^ 8 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (289 / 4 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
  have l1 : (64 : ℝ) ^ 1 ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (289 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
  have l2 : (64 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (289 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
  have l3 : (64 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (289 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
  have l4 : (64 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have hc0 : (122385829 : ℝ) ≤ -x ^ 4 - 486 * x ^ 3 - 51369 * x ^ 2 + (258812636 / 25) * x - (1537035264 / 25) := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have hc1 : (1572145996 : ℝ) ≤ -4 * x ^ 3 - 14888 * x ^ 2 + 26492060 * x - (1103023872 / 25) := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t1 : 0 ≤ (-4 * x ^ 3 - 14888 * x ^ 2 + 26492060 * x - (1103023872 / 25)) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (886591980 : ℝ) ≤ -4 * x ^ 3 - 494 * x ^ 2 + 14525758 * x - (974230564 / 25) := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t2 : 0 ≤ (-4 * x ^ 3 - 494 * x ^ 2 + 14525758 * x - (974230564 / 25)) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (-3547781 : ℝ) ≤ -12 * x ^ 2 - 8640 * x - 2860900 := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t3 : (-3547781 : ℝ) ≤ (-12 * x ^ 2 - 8640 * x - 2860900) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (14714126 : ℝ) ≤ -6 * x ^ 2 + 470 * x + 14715367 := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t4 : 0 ≤ (-6 * x ^ 2 + 470 * x + 14715367) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (5381 : ℝ) ≤ -12 * x + 6248 := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t5 : 0 ≤ (-12 * x + 6248) * g ^ 5 := mul_nonneg (by linarith) (by positivity)
  have hc6 : (189 : ℝ) ≤ -4 * x + 478 := by norm_num at u1 u2 u3 u4 l1 l2 l3 l4 ⊢; linarith
  have t6 : 0 ≤ (-4 * x + 478) * g ^ 6 := mul_nonneg (by linarith) (by positivity)
  have hc7 : (-4 : ℝ) ≤ -4 := le_refl _
  have t7 : (-4 : ℝ) ≤ (-4) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-1 : ℝ) ≤ -1 := le_refl _
  have t8 : (-1 : ℝ) ≤ (-1) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  linarith

/-- The box polynomial for the main term `H = N / (5760 (s - 1))`, proved. -/
lemma box_two_poly (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 8 ≤ t) (ht1 : t ≤ 17 / 2) :
    ((-σ ^ 4 - 2 * σ ^ 3 + 6 * σ ^ 2 * t ^ 2 + 241 * σ ^ 2 + 6 * σ * t ^ 2 + 2642 * σ - t ^ 4 - 241 * t ^ 2 + 8640) ^ 2 + (2 * t * (-2 * σ ^ 3 - 3 * σ ^ 2 + 2 * σ * t ^ 2 + 241 * σ + t ^ 2 + 1321)) ^ 2) <
      (63 / 100 + 2 * σ / 3) ^ 2 * 5760 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) := by
  have hx0 : 64 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 289 / 4 := by nlinarith
  have h := coeff_two_pos σ (t ^ 2) h0 h1 hx0 hx1
  have e : (63 / 100 + 2 * σ / 3) ^ 2 * 5760 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) -
      ((-σ ^ 4 - 2 * σ ^ 3 + 6 * σ ^ 2 * t ^ 2 + 241 * σ ^ 2 + 6 * σ * t ^ 2 + 2642 * σ - t ^ 4 - 241 * t ^ 2 + 8640) ^ 2 + (2 * t * (-2 * σ ^ 3 - 3 * σ ^ 2 + 2 * σ * t ^ 2 + 241 * σ + t ^ 2 + 1321)) ^ 2) =
      (-(t ^ 2) ^ 4 - 486 * (t ^ 2) ^ 3 - 51369 * (t ^ 2) ^ 2 + (258812636 / 25) * t ^ 2 - (1537035264 / 25)) +
      (-4 * (t ^ 2) ^ 3 - 14888 * (t ^ 2) ^ 2 + 26492060 * t ^ 2 - (1103023872 / 25)) * σ +
      (-4 * (t ^ 2) ^ 3 - 494 * (t ^ 2) ^ 2 + 14525758 * t ^ 2 - (974230564 / 25)) * σ ^ 2 +
      (-12 * (t ^ 2) ^ 2 - 8640 * t ^ 2 - 2860900) * σ ^ 3 +
      (-6 * (t ^ 2) ^ 2 + 470 * t ^ 2 + 14715367) * σ ^ 4 +
      (-12 * t ^ 2 + 6248) * σ ^ 5 +
      (-4 * t ^ 2 + 478) * σ ^ 6 +
      (-4) * σ ^ 7 +
      (-1) * σ ^ 8 := by ring
  linarith

/-- The main term is small: `‖H(s)‖ < 63/100 + 2σ/3` on `(0,1) × (8, 17/2]`. Proved. -/
lemma main_two_lt (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 8 < s.im) (ht1 : s.im ≤ 17 / 2) :
    ‖1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760‖ < 63 / 100 + 2 * s.re / 3 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : 1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 =
      (2880 * (s - 1) + 11520 + 240 * s * (s - 1) - (s - 1) * s * (s + 1) * (s + 2)) /
        (5760 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  rw [div_lt_iff₀ (by positivity)]
  set P : ℂ := 2880 * (s - 1) + 11520 + 240 * s * (s - 1) - (s - 1) * s * (s + 1) * (s + 2) with hP
  have hPre : P.re = -s.re ^ 4 - 2 * s.re ^ 3 + 6 * s.re ^ 2 * s.im ^ 2 + 241 * s.re ^ 2 + 6 * s.re * s.im ^ 2 + 2642 * s.re - s.im ^ 4 - 241 * s.im ^ 2 + 8640 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = 2 * s.im * (-2 * s.re ^ 3 - 3 * s.re ^ 2 + 2 * s.re * s.im ^ 2 + 241 * s.re + s.im ^ 2 + 1321) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hc : 0 < (63 / 100 + 2 * s.re / 3) * (5760 * ‖s - 1‖) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hc.le
  have e1 : ((63 / 100 + 2 * s.re / 3) * (5760 * ‖s - 1‖)) ^ 2 =
      (63 / 100 + 2 * s.re / 3) ^ 2 * 5760 ^ 2 * ((s.re - 1) ^ 2 + s.im ^ 2) := by
    rw [mul_pow, mul_pow, hsq (s - 1)]
    simp
    ring
  rw [e1, hsq P, hPre, hPim]
  exact box_two_poly s.re s.im h0.le h1.le ht0.le ht1

/-- The remainder factor is small: `‖s‖ ‖s+1‖ ‖s+2‖ ‖s+3‖ ≤ 6393` on the box. Proved. -/
lemma prod_two_le (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 8 < s.im) (ht1 : s.im ≤ 17 / 2) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ ≤ 6393 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have ht2 : s.im ^ 2 ≤ 289 / 4 := by nlinarith
  have n0 : ‖s‖ ^ 2 ≤ 293 / 4 := by rw [hsq]; nlinarith
  have n1 : ‖s + 1‖ ^ 2 ≤ 305 / 4 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have n2 : ‖s + 2‖ ^ 2 ≤ 325 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n3 : ‖s + 3‖ ^ 2 ≤ 353 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 ≤ 293 / 4 * (305 / 4) * (325 / 4) * (353 / 4) := by
    have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 =
        ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 := by ring
    rw [e]
    have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
    have q2 := mul_le_mul q1 n2 (by positivity) (by norm_num)
    exact mul_le_mul q2 n3 (by positivity) (by norm_num)
  have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) ^ 2 ≤ 6393 ^ 2 := by
    refine hsq'.trans ?_; norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp this

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `8 < Im ρ ≤ 17/2`. At a zero,
`2^(-ρ) H(ρ) = Q - 1` with `Q` the remainder of `riemannZeta_eq_EM4_two`, so
`‖H‖ ≥ 2^σ - 2^σ ‖Q‖ ≥ 1 + 2σ/3 - 37/100`, against `main_two_lt`. -/
theorem riemannZeta_ne_zero_eight_seventeen_half (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 8 < ρ.im) (ht1 : ρ.im ≤ 17 / 2) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM4_two h0 hρ1
  set I := ∫ x in Ioi (2 : ℝ),
    ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) *
      (x : ℂ) ^ (-ρ - 4) with hI
  set H := 1 / 2 + 2 / (ρ - 1) + ρ / 24 - ρ * (ρ + 1) * (ρ + 2) / 5760 with hH
  set Q := ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) / 2 * I with hQ
  have hkey : (2 : ℂ) ^ (-ρ) * H = Q - 1 := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 360 * (2 : ℝ) ^ ((-ρ - 4).re + 1) / (-(-ρ - 4).re - 1) :=
    norm_weight_int_le2 (by fun_prop) abs_B4_le (by simp; linarith)
  have hre1 : (-ρ - 4).re + 1 = -ρ.re - 3 := by simp; ring
  have hre2 : (-(-ρ - 4).re - 1) = ρ.re + 3 := by simp; ring
  rw [hre1, hre2] at hIle
  have hn2 : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-ρ)
    simpa using this
  have hP := prod_two_le ρ h0 h1 ht0 ht1
  have hσ : 0 < ρ.re + 3 := by linarith
  have hQle : ‖Q‖ ≤ 6393 / 2 * (1 / 360 * (2 : ℝ) ^ (-ρ.re - 3) / (ρ.re + 3)) := by
    rw [hQ, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, norm_mul, norm_mul]
    have hpos : 0 ≤ (2 : ℝ) ^ (-ρ.re - 3) := Real.rpow_nonneg (by norm_num) _
    have hIn : 0 ≤ ‖I‖ := norm_nonneg _
    have hA : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ := by positivity
    calc ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ / 2 * ‖I‖
        ≤ 6393 / 2 * ‖I‖ := by
          apply mul_le_mul_of_nonneg_right _ hIn; linarith
      _ ≤ 6393 / 2 * (1 / 360 * (2 : ℝ) ^ (-ρ.re - 3) / (ρ.re + 3)) :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  -- multiply through by 2^σ
  have hsplit : (2 : ℝ) ^ (-ρ.re - 3) = (2 : ℝ) ^ (-ρ.re) / 8 := by
    rw [sub_eq_add_neg, Real.rpow_add two_pos]
    rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
    ring
  have hu : (2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add two_pos]; simp
  have hupos : 0 < (2 : ℝ) ^ ρ.re := Real.rpow_pos_of_pos two_pos _
  have hvpos : 0 < (2 : ℝ) ^ (-ρ.re) := Real.rpow_pos_of_pos two_pos _
  have hlow : 1 - ‖Q‖ ≤ (2 : ℝ) ^ (-ρ.re) * ‖H‖ := by
    have ha := norm_sub_norm_le (1 : ℂ) Q
    rw [norm_sub_rev, norm_one] at ha
    have hb : ‖Q - 1‖ = (2 : ℝ) ^ (-ρ.re) * ‖H‖ := by
      rw [← hkey, norm_mul, hn2]
    linarith
  have hE : (2 : ℝ) ^ ρ.re * ‖Q‖ ≤ 37 / 100 := by
    have := mul_le_mul_of_nonneg_left hQle hupos.le
    rw [hsplit] at this
    have e : (2 : ℝ) ^ ρ.re * (6393 / 2 * (1 / 360 * ((2 : ℝ) ^ (-ρ.re) / 8) / (ρ.re + 3))) =
        6393 / 5760 / (ρ.re + 3) * ((2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re)) := by
      field_simp
      ring
    rw [e, hu, mul_one] at this
    have : 6393 / 5760 / (ρ.re + 3) ≤ 37 / 100 := by
      rw [div_le_iff₀ hσ]; nlinarith
    linarith
  have hH2 : (2 : ℝ) ^ ρ.re - 37 / 100 ≤ ‖H‖ := by
    have := mul_le_mul_of_nonneg_left hlow hupos.le
    have e : (2 : ℝ) ^ ρ.re * ((2 : ℝ) ^ (-ρ.re) * ‖H‖) = ‖H‖ := by
      rw [← mul_assoc, hu, one_mul]
    rw [e, mul_sub, mul_one] at this
    linarith
  have hlo := two_rpow_ge ρ.re h0.le
  have hup := main_two_lt ρ h0 h1 ht0 ht1
  rw [← hH] at hup
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(17/2, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(17/2, 21/2]`. Class MEDIUM: the route of this file with
more Bernoulli terms, three up to `19/2` and up to six near `21/2`, S137 grid numerics. -/
theorem zeta_zero_free_seventeen_half_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 17 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- `Feed1122ZetaEight.zeta_zero_free_eight_ten_half`, exactly its statement, from the proved
range `(8, 17/2]` and the MEDIUM leaf on `(17/2, 21/2]`. -/
theorem zeta_zero_free_eight_ten_half_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 8 < ρ.im) : 21 / 2 < ρ.im := by
  by_cases h : ρ.im ≤ 17 / 2
  · exact absurd h0 (riemannZeta_ne_zero_eight_seventeen_half ρ hre0 hre1 him h)
  · exact zeta_zero_free_seventeen_half_ten_half ρ h0 hre0 hre1 (not_le.mp h)

end LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo
