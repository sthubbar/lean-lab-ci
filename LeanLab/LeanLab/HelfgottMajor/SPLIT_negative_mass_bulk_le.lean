import LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw

/-!
Split of `negative_mass_bulk_le` in `LeanLab.HelfgottMajor.SPLIT_negative_sampling_raw`
into three leaves.

The sealed statement bounds the negative middle zero mass restricted to ordinates at most
minus three halves, that is the whole negative half above the short window, by two Cauchy
Schwarz comparisons against the negative critical line energy and the negative derivative
energy, each against an unevaluated finite logarithmic weight integral.

The split separates the jobs the sealed statement does at once. The first leaf is the
sampling step: the multiplicity weighted sum of the Gaussian Mellin norms at the zeros of
the negative half is at most the two height integrals of the same weights taken over the
line, one against the mean weight and one against the derivative weight. It produces
linear weights and no square root factor. The second and third leaves are the two Cauchy
Schwarz comparisons of those two height integrals against the line energy and the
derivative energy; they involve no character, no zero and no multiplicity.

`negative_mass_bulk_le_split` assembles the sealed statement from the three leaves: the
summand is rewritten on the critical line, the two height integrals are bounded, and the
bounds are added. It has no sorry of its own. All three leaves are OPEN.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform

/-- LEAF 1 of 3. The sampling step of the negative half. The multiplicity weighted sum of
the Gaussian Mellin norms over the zeros with ordinate at most minus three halves and
absolute ordinate at most `T` is at most the two height integrals over the positive
ordinates from one to `T`: the critical line norm against the mean weight divided by
`2 * π`, and the derivative norm against the shifted log weight. Both integrals are left
in place and neither energy, neither square root and neither endpoint value enters. -/
theorem negative_bulk_mass_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) := by
  sorry

/-! ### Continuity of the Gaussian Mellin transform on the critical line -/

/-- The Gaussian Mellin transform is continuous along the critical line with the plus sign, as
a Fourier integral of the log-coordinate profile. -/
private lemma continuous_gaussianMellin_line_plus (δ : ℝ) :
    Continuous (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) := by
  have hF : Continuous (𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (log_integrable δ)
  have hcomp : Continuous (fun t : ℝ => 𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(t / (2 * π)))) :=
    hF.comp (by fun_prop)
  refine hcomp.congr fun t => ?_
  exact (mellin_eq_fourier_gauss δ t).symm

/-- The norm of the Gaussian Mellin transform is continuous along the critical line with the
minus sign, which is the sign used by the negative half. -/
private lemma continuous_norm_gaussianMellin_line_minus (δ : ℝ) :
    Continuous (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖) := by
  have hp : Continuous (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)) :=
    continuous_gaussianMellin_line_plus δ
  have hn : Continuous (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) *
      Complex.I)) := hp.comp (by fun_prop)
  refine hn.norm.congr fun t => ?_
  have hArg : ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) - (t : ℝ) * Complex.I) := by
    push_cast
    ring
  rw [hArg]

/-! ### Interval Cauchy Schwarz against an energy integral -/

/-- Interval Cauchy Schwarz with the first square energy extended to the upper half line from
zero. -/
private lemma interval_mul_le_energy_of_integrable (f g : ℝ → ℝ) (a T : ℝ) (ha : a ≤ 1)
    (hT : 1 ≤ T) (hfint : IntegrableOn (fun t => f t ^ 2) (Ioi a))
    (hfc : ContinuousOn f (Icc 1 T)) (hgc : ContinuousOn g (Icc 1 T)) :
    (∫ t in (1 : ℝ)..T, f t * g t) ≤
      sqrt (∫ t in Ioi a, f t ^ 2) * sqrt (∫ t in (1 : ℝ)..T, g t ^ 2) := by
  have hfI : MemLp f 2 (volume.restrict (Ioc 1 T)) := by
    apply (memLp_two_iff_integrable_sq_norm
      ((hfc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
    exact ((hfc.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hgI : MemLp g 2 (volume.restrict (Ioc 1 T)) := by
    apply (memLp_two_iff_integrable_sq_norm
      ((hgc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
    exact ((hgc.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcmp : (∫ t in Ioc (1 : ℝ) T, f t * g t) ≤
      ∫ t in Ioc (1 : ℝ) T, ‖f t‖ * ‖g t‖ := by
    apply integral_mono_ae (hfI.integrable_mul hgI) (hfI.norm.integrable_mul hgI.norm)
    filter_upwards [] with t
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using! le_abs_self (f t * g t)
  have hcs := integral_mul_norm_le_Lp_mul_Lq (f := f) (g := g)
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (by simpa using hfI) (by simpa using hgI)
  simp only [Real.norm_eq_abs, rpow_two, sq_abs, ← sqrt_eq_rpow] at hcs
  have he : (∫ t in Ioc (1 : ℝ) T, f t ^ 2) ≤ ∫ t in Ioi a, f t ^ 2 := by
    apply setIntegral_mono_set hfint (Eventually.of_forall fun t => sq_nonneg (f t))
    exact Eventually.of_forall fun t ht => lt_of_le_of_lt ha ht.1
  simp only [intervalIntegral.integral_of_le hT]
  exact (hcmp.trans hcs).trans (mul_le_mul_of_nonneg_right
    (sqrt_le_sqrt he) (sqrt_nonneg _))

/-- LEAF 2 of 3. Cauchy Schwarz on the height interval against the critical line energy of
the negative half. The mean weight integral of the critical line norms divided by
`2 * π` is at most the square root of the negative line energy times the square root of the
squared mean weight integral. Only the interval from one to `T` inside the positive half
line is used, so no character hypothesis and no zero hypothesis enters. -/
theorem negative_bulk_main_weight_cauchy (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
  have hc := continuous_norm_gaussianMellin_line_minus δ
  have hfint : IntegrableOn
      (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2) (Ioi 0) := by
    have hp : Integrable (fun t : ℝ =>
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
      Decomp389b.integrable_mellin_sq δ
    have hn : Integrable (fun t : ℝ =>
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2) :=
      hp.comp_neg
    have hfun : (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2)
        = fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2 := by
      funext t
      refine congrArg (fun z => ‖gaussianMellin δ z‖ ^ 2) ?_
      push_cast
      ring
    rw [hfun] at hn
    exact hn.restrict
  have hg : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t / (2 * π))) (Icc 1 T) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log (by fun_prop)
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    exact ne_of_gt (by have := ht.1; positivity)
  have h0 : (0 : ℝ) ≤ 1 := by norm_num
  have hh := interval_mul_le_energy_of_integrable _ _ 0 T h0 hT hfint hc.continuousOn hg
  have hE : lineEnergy δ (-1) = ∫ t in Ioi 0,
      ‖gaussianMellin δ ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [lineEnergy]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    refine congrArg (fun z => ‖gaussianMellin δ z‖ ^ 2) ?_
    push_cast
    ring
  rw [hE]
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1 / (2 * π))
  refine hm.trans_eq ?_
  rw [div_eq_mul_inv]
  ring


/-- The Gaussian-character integrand of `gaussianMellin`, as a function of one variable. -/
private lemma gcont (δ : ℝ) :
    Continuous (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) := by
  unfold e
  fun_prop

/-- Super-polynomial decay of the Gaussian at infinity. -/
private lemma gisBigO_top (δ : ℝ) :
    (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) =O[Filter.atTop]
      (fun x : ℝ => x ^ (-(1 : ℝ))) := by
  have h1 : (fun x : ℝ => Real.exp (-x ^ 2 / 2)) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-x)) := by
    refine (exp_neg_mul_sq_isLittleO_exp_neg (b := 1 / 2) (by norm_num)).congr' ?_ ?_
    · filter_upwards with x
      congr 1
      ring
    · filter_upwards with x
      rfl
  have h2 : (fun x : ℝ => Real.exp (-x)) =o[Filter.atTop] (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    simpa only [one_mul, neg_mul] using
      isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-1)
  have h3 := (h1.trans h2).isBigO
  rw [← isBigO_norm_left]
  refine h3.congr' (Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => rfl)
  exact (gauss_norm δ x).symm

/-- Boundedness of the Gaussian-character integrand at the origin. -/
private lemma gisBigO_bot (δ : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hmem : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
  filter_upwards [hmem, self_mem_nhdsWithin] with x hx1 hx
  simp only [gauss_norm, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx (-b)),
    one_mul]
  refine le_trans (Real.exp_le_one_iff.mpr ?_)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (le_of_lt hx1) (by linarith))
  have := sq_nonneg x
  nlinarith

/-- Differentiation under the Mellin integral for the Gaussian-character integrand. -/
private lemma gmellin_hasDerivAt (δ : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s) s := by
  have hfc : LocallyIntegrableOn (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
      (Set.Ioi 0) :=
    (gcont δ).locallyIntegrable.locallyIntegrableOn _
  exact (mellin_hasDerivAt_of_isBigO_rpow hfc (gisBigO_top δ) hs1
    (gisBigO_bot δ (by linarith : (0:ℝ) < s.re / 2)) (by linarith)).2

/-- The log-coordinate profile of the derivative of the Gaussian Mellin transform. -/
private lemma wcont (δ : ℝ) :
    Continuous (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  unfold e
  fun_prop

/-- The Mellin transform of the log-weighted Gaussian-character integrand on the critical line is
the Fourier integral of its log-coordinate transform. -/
private lemma mellin_log_eq_fourier' (δ t : ℝ) :
    mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
        ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(t / (2 * π))) := by
  rw [mellin, fourier_eq']
  rw [← Real.range_exp, ← Set.image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy)]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, RCLike.real_smul_eq_coe_mul, smul_eq_mul, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), Complex.ofReal_exp, Real.log_exp]
  simp only [inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    abs_of_pos (exp_pos u)]
  set G : ℂ := (exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u) with hGdef
  set s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I with hsdef
  have hL : ((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * G)
      = Complex.exp ((u : ℂ) * s) * G := by
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hR : Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
      (((exp (u / 2) : ℝ) : ℂ) * G)
      = Complex.exp ((u : ℂ) * s) * G := by
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp only [← Complex.ofReal_exp]
  calc ((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * ((u : ℂ) * G))
      = (u : ℂ) * (((exp u : ℝ) : ℂ) * (Complex.exp ((u : ℂ) * (s - 1)) * G)) := by ring
    _ = (u : ℂ) * (Complex.exp ((u : ℂ) * s) * G) := by rw [hL]
    _ = (u : ℂ) * (Complex.exp ((-2 : ℂ) * (π : ℂ) *
          ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) * (((exp (u / 2) : ℝ) : ℂ) * G)) := by
        rw [hR]
    _ = Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
          ((u : ℂ) * (((exp (u / 2) : ℝ) : ℂ) * G)) := by ring

/-- Pointwise norm of the log-coordinate derivative profile. -/
private lemma wnorm (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = |u| * (exp (u / 2) * exp (-(exp u) ^ 2 / 2)) := by
  rw [norm_mul, log_norm, Complex.norm_real, Real.norm_eq_abs]

/-- Pointwise square norm of the log-coordinate derivative profile. -/
private lemma wnorm_sq (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = u ^ 2 * (exp u * exp (-(exp u) ^ 2)) := by
  rw [wnorm, mul_pow, mul_pow, sq_abs]
  congr 1
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

/-- The log-coordinate derivative profile is dominated by a decaying exponential. -/
private lemma wle (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤
      4 * exp (-(1 / 4 : ℝ) * |u|) := by
  rw [wnorm]
  have h1 : exp (u / 2) * exp (-(exp u) ^ 2 / 2) ≤ exp (-|u| / 2) := by
    rw [← log_norm]
    exact log_le_exp_abs δ u
  refine (mul_le_mul_of_nonneg_left h1 (abs_nonneg u)).trans ?_
  have hexp : 1 + |u| / 4 ≤ exp (|u| / 4) := by
    linarith [Real.add_one_le_exp (|u| / 4)]
  have hkey : |u| * exp (-|u| / 4) ≤ 4 := by
    have hp := exp_pos (-|u| / 4)
    have h4 : (1 + |u| / 4) * exp (-|u| / 4) ≤ 1 := by
      have h5 := mul_le_mul_of_nonneg_right hexp (le_of_lt hp)
      rw [← Real.exp_add, show |u| / 4 + -|u| / 4 = 0 by ring, Real.exp_zero] at h5
      exact h5
    nlinarith [h4, hp, abs_nonneg u]
  have hmul : exp (-|u| / 2) = exp (-|u| / 4) * exp (-|u| / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp := exp_pos (-|u| / 4)
  rw [hmul, show -(1 / 4 : ℝ) * |u| = -|u| / 4 by ring]
  nlinarith [hkey, hp]

/-- The log-coordinate derivative profile is integrable. -/
private lemma wintegrable (δ : ℝ) :
    Integrable (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  refine Integrable.mono' ((integrable_exp_neg_abs_mul (c := 1 / 4) (by norm_num)).const_mul 4)
    (wcont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact wle δ u

/-- The log-coordinate derivative profile lies in `L2`. -/
private lemma wmemLp (δ : ℝ) :
    MemLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) 2 := by
  have hcont : Continuous (fun u : ℝ => 4 * exp (-(1 / 4 : ℝ) * |u|)) := by fun_prop
  have hg : MemLp (fun u : ℝ => 4 * exp (-(1 / 4 : ℝ) * |u|)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    have heq : (fun u : ℝ => ‖4 * exp (-(1 / 4 : ℝ) * |u|)‖ ^ 2)
        = fun u : ℝ => 16 * exp (-(1 / 2 : ℝ) * |u|) := by
      funext u
      have hp : (0:ℝ) < 4 * exp (-(1 / 4 : ℝ) * |u|) := by positivity
      rw [Real.norm_eq_abs, abs_of_pos hp, mul_pow, show (4:ℝ) ^ 2 = 16 by norm_num,
        show exp (-(1 / 4 : ℝ) * |u|) ^ 2 = exp (-(1 / 2 : ℝ) * |u|) by
          rw [sq, ← Real.exp_add]; congr 1; ring]
    rw [heq]
    exact (integrable_exp_neg_abs_mul (c := 1 / 2) (by norm_num)).const_mul 16
  refine MemLp.mono' hg (wcont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact wle δ u

/-- The `L2` mass of the log-coordinate derivative profile is the log squared Gaussian moment. -/
private lemma wsq_integral (δ : ℝ) :
    ∫ u : ℝ, ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2 = Sec45.nLog := by
  have himg : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) * Real.log x ^ 2
      = ∫ u : ℝ, exp u • (Real.exp (-(exp u) ^ 2) * Real.log (exp u) ^ 2) := by
    rw [← Real.range_exp, ← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.exp_injective hxy)]
    simp only [abs_of_pos (exp_pos _), setIntegral_univ]
  rw [show (∫ u : ℝ, ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2)
      = ∫ u : ℝ, exp u • (Real.exp (-(exp u) ^ 2) * Real.log (exp u) ^ 2) from by
    apply integral_congr_ae
    filter_upwards with u
    rw [wnorm_sq, Real.log_exp, smul_eq_mul]
    ring]
  rw [← himg]
  exact LeanLab.HelfgottMajor.LogMoment431.gaussian_log_square_integral

/-- The Fourier profile of the derivative has integrable square. -/
private lemma integrable_fourier_sq_weighted' (δ : ℝ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) := by
  have h2 := wmemLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (wintegrable δ)
    (wmemLp δ)] with ξ hξ
  rw [hξ]

/-- The Fourier side square integral of the derivative profile. -/
private lemma fourier_sq_integral_weighted' (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) y‖ ^ 2 = Sec45.nLog := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (wintegrable δ) (wmemLp δ)]
  exact wsq_integral δ

/-- The pointwise critical-line identity for the derivative. -/
private lemma deriv_mellin_sq_pointwise' (δ t : ℝ) :
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [(gmellin_hasDerivAt δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num)).deriv, mellin_log_eq_fourier' δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

/-- The derivative of the Gaussian Mellin transform has integrable square on the critical line. -/
private lemma integrable_deriv_mellin_sq' (δ : ℝ) :
    Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
      ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) hR).mpr
      (integrable_fourier_sq_weighted' δ)
  refine h.congr ?_
  filter_upwards with t
  exact (deriv_mellin_sq_pointwise' δ t).symm


/-! ### Continuity of the derivative of the Gaussian Mellin transform -/

/-- The derivative of the Gaussian Mellin transform on the critical line, as the Fourier integral
of the log-coordinate profile. -/
private lemma deriv_mellin_eq_fourier' (δ t : ℝ) :
    deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(t / (2 * π))) := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [(gmellin_hasDerivAt δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num)).deriv, mellin_log_eq_fourier' δ t]

/-- Continuity of the derivative of the Gaussian Mellin transform on the critical line. -/
private lemma continuous_deriv_mellin_line_plus' (δ : ℝ) :
    Continuous (fun t : ℝ => deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) := by
  have hF : Continuous (𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (wintegrable δ)
  have hcomp : Continuous (fun t : ℝ => 𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(t / (2 * π)))) :=
    hF.comp (by fun_prop)
  refine hcomp.congr fun t => ?_
  exact (deriv_mellin_eq_fourier' δ t).symm

/-- Continuity of the norm of the derivative of the Gaussian Mellin transform on the negative
critical line. -/
private lemma continuous_norm_deriv_mellin_minus' (δ : ℝ) :
    Continuous (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖) := by
  have hp := continuous_deriv_mellin_line_plus' δ
  have hn : Continuous (fun t : ℝ =>
      deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) :=
    hp.comp (by fun_prop)
  refine hn.norm.congr fun t => ?_
  have hArg : ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) - (t : ℝ) * Complex.I) := by
    push_cast
    ring
  rw [hArg]

/-- LEAF 3 of 3. Cauchy Schwarz on the height interval against the derivative energy of the
negative half. The integral of the derivative norms against the shifted log weight is at
most the square root of the negative derivative energy times the square root of the squared
shifted weight integral. As in the second leaf, no character and no zero enters, and no
critical line energy is used. -/
theorem negative_bulk_error_weight_cauchy (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) ≤
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  have hc := continuous_norm_deriv_mellin_minus' δ
  have hfint : IntegrableOn (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2) (Ioi 1) := by
    have hp : Integrable (fun t : ℝ =>
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
      integrable_deriv_mellin_sq' δ
    have hn : Integrable (fun t : ℝ =>
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2) :=
      hp.comp_neg
    have hfun : (fun t : ℝ =>
          ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2)
        = fun t : ℝ => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2 := by
      funext t
      refine congrArg (fun z => ‖deriv (gaussianMellin δ) z‖ ^ 2) ?_
      push_cast
      ring
    rw [hfun] at hn
    exact hn.restrict
  have hg : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389) (Icc 1 T) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have ht0 : 0 < t := by have := ht.1; linarith
    fun_prop (disch := positivity)
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have hh := interval_mul_le_energy_of_integrable _ _ 1 T h1 hT hfint hc.continuousOn hg
  have hE : derivativeEnergy δ (-1) = ∫ t in Ioi 1,
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) - (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [derivativeEnergy]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    refine congrArg (fun z => ‖deriv (gaussianMellin δ) z‖ ^ 2) ?_
    push_cast
    ring
  rw [hE]
  exact hh

/-- The sealed statement of `negative_mass_bulk_le`, assembled from the three leaves. The
critical line hypothesis rewrites every summand to the multiplicity weighted Mellin norm at
the ordinate, the sampling leaf bounds the sum by the two height integrals, and the two
Cauchy Schwarz leaves bound those integrals by the two energies. -/
theorem negative_mass_bulk_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)}
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ) ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  classical
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I)‖) ρ =
      Set.indicator {ρ | ρ.val.im ≤ -(3 / 2)} (fun ρ => mellinMassTerm χ δ ρ.val) ρ := by
    intro ρ
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hρeq : ρ.val = (1 / 2 : ℂ) + (ρ.val.im : ℝ) * Complex.I := by
      refine Complex.ext ?_ ?_
      · simpa using hz
      · simp
    by_cases hp : ρ.val.im ≤ -(3 / 2)
    · rw [Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp),
        Set.indicator_of_mem (show ρ ∈ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp)]
      rw [mellinMassTerm]
      have him : ∀ r : ℝ, ((1 / 2 : ℂ) + (r : ℂ) * Complex.I).im = r := by
        intro r
        simp
      rw [hρeq, him]
    · rw [Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp),
        Set.indicator_of_notMem (show ρ ∉ {ρ : {ρ : ℂ //
          DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} |
          ρ.val.im ≤ -(3 / 2)} from hp)]
  rw [tsum_congr hpt]
  exact (negative_bulk_mass_integral q χ hχ δ T hT hlarge hzeros).trans
    (add_le_add (negative_bulk_main_weight_cauchy q δ T hT)
      (negative_bulk_error_weight_cauchy q δ T hT))

end LeanLab.HelfgottMajor.Decomp431a

#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_mass_bulk_le_split
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_mass_integral
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_main_weight_cauchy
#print axioms LeanLab.HelfgottMajor.Decomp431a.negative_bulk_error_weight_cauchy
