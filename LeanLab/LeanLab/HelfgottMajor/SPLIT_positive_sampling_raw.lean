import LeanLab.HelfgottMajor.Decomp431a

/-!
Split of the positive signed zero sampling inequality of `Decomp431a.positive_sampling_raw`.

The sealed inequality bounds the positive signed Mellin mass attached to the zeros of a
primitive Dirichlet `L`-function in the strip `0 < re < 1` below height `T`, with imaginary
part above `1`, by a sum of three terms: a main term carrying the square root of the
critical line energy and the square root of the squared logarithmic height weight, an error
term carrying the square root of the derivative energy and the square root of the squared
shifted log weight, and an endpoint term at height `1`.

The split proceeds in two stages.  First the signed mass is replaced by the sum of the
absolute values of its summands, so that every summand enters with a sign (stage one).
Second, that nonnegative zero sum is turned into three line integrals over the height
interval `[1, T]` (stage two).  The two square root factors are then obtained by Cauchy
Schwarz on the height interval: one against the critical line energy, one against the
derivative energy above height `1`.  Each leaf below is one of those steps.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-! ### Private helpers for the two interval Cauchy–Schwarz leaves -/

/-- A product of two `L²` functions is integrable (AM–GM domination). -/
private lemma integrable_mul_of_memLp_two {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    MeasureTheory.Integrable (fun x => f x * g x) (MeasureTheory.volume.restrict s) := by
  have hf2 : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdom : MeasureTheory.Integrable
      (fun x => (‖f x‖ ^ 2 + ‖g x‖ ^ 2) / 2) (MeasureTheory.volume.restrict s) :=
    (hf2.add hg2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  have hsq : 0 ≤ (‖f x‖ - ‖g x‖) ^ 2 := sq_nonneg _
  rw [norm_mul]
  nlinarith [norm_nonneg (f x), norm_nonneg (g x), hsq]

/-- The norm product of two `L²` functions is integrable. -/
private lemma integrable_norm_mul_of_memLp_two {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    MeasureTheory.Integrable (fun x => ‖f x‖ * ‖g x‖) (MeasureTheory.volume.restrict s) := by
  have hf2 : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdom : MeasureTheory.Integrable
      (fun x => (‖f x‖ ^ 2 + ‖g x‖ ^ 2) / 2) (MeasureTheory.volume.restrict s) :=
    (hf2.add hg2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    ((hf.aestronglyMeasurable.norm).mul (hg.aestronglyMeasurable.norm)) ?_
  filter_upwards with x
  have hsq : 0 ≤ (‖f x‖ - ‖g x‖) ^ 2 := sq_nonneg _
  have h1 : ‖‖f x‖ * ‖g x‖‖ = ‖f x‖ * ‖g x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [h1]
  nlinarith [norm_nonneg (f x), norm_nonneg (g x), hsq]

/-- Cauchy–Schwarz in integral form: `∫ f g ≤ √(∫ f²) √(∫ g²)` on a set. -/
private lemma setIntegral_mul_le_sqrt {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    ∫ x in s, f x * g x ≤ sqrt (∫ x in s, f x ^ 2) * sqrt (∫ x in s, g x ^ 2) := by
  have hHolder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := MeasureTheory.volume.restrict s) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (by simpa using hf) (by simpa using hg)
  have hmono : (∫ x in s, f x * g x) ≤ ∫ x in s, ‖f x‖ * ‖g x‖ := by
    refine MeasureTheory.integral_mono_ae (integrable_mul_of_memLp_two hf hg)
      (integrable_norm_mul_of_memLp_two hf hg) (Filter.Eventually.of_forall (fun x => ?_))
    refine (le_abs_self (f x * g x)).trans_eq ?_
    simp only [abs_mul, Real.norm_eq_abs]
  refine hmono.trans (hHolder.trans (le_of_eq ?_))
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have hsq1 : (∫ a in s, ‖f a‖ ^ (2 : ℝ)) = ∫ x in s, f x ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [← h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hsq2 : (∫ a in s, ‖g a‖ ^ (2 : ℝ)) = ∫ x in s, g x ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [← h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [hsq1, hsq2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]


/-- LEAF. Stage one, sign removal: the positive signed zero mass is at most the sum over the
same zero set of the absolute values of its summands, each restricted to imaginary part
above `1`.  This is the triangle inequality for a nonnegative summand family; it uses no
analytic input and no hypothesis on the zeros. -/
theorem positive_mass_le_norm_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    positiveMass χ δ T ≤
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
  classical
  have hkey : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ
        = ‖Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ‖ := by
    intro ρ
    by_cases hp : 1 < ρ.val.im <;> simp [Set.indicator, hp]
  simp only [hkey]
  unfold positiveMass
  by_cases hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
      Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ)
  · refine le_trans ?_ (norm_tsum_le_tsum_norm hs.norm)
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  · rw [tsum_eq_zero_of_not_summable hs]
    exact tsum_nonneg (fun ρ => norm_nonneg _)

/-- LEAF. Stage two, zero sum to line integral: the nonnegative sum of the Mellin masses at
the positive zeros below height `T` is at most the sum of the three height integrals over
`[1, T]` that appear on the right: the mean weight integral of the critical line values, the
integral of the derivative values against the shifted log weight, and the endpoint value at
height `1` against the log of the modulus.  This is the sampling step; it produces linear
weights and no square root factor yet. -/
theorem positive_mass_norm_sum_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- LEAF. Cauchy Schwarz on the height interval against the critical line energy: the mean
weight integral of the critical line values, divided by `2 * π`, is at most the square root
of the line energy times the square root of the squared logarithmic weight integral.  Only
`[1, T]` inside the positive half line is used, so this leaf has no character or zero
hypothesis; it is a two function estimate with a nonnegative pair. -/
theorem main_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set F : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ with hF
  set W : ℝ → ℝ := fun t => log ((q : ℝ) * t / (2 * π)) with hW
  show (1 / (2 * π)) * (∫ t in (1 : ℝ)..T, F t * W t) ≤
    sqrt (lineEnergy δ 1) / (2 * π) * sqrt (∫ t in (1 : ℝ)..T, W t ^ 2)
  have hGsq : MeasureTheory.Integrable (fun t : ℝ => F t ^ 2) := by
    simpa only [hF] using integrable_mellin_sq δ
  have hline : lineEnergy δ 1 = ∫ t in Set.Ioi (0 : ℝ), F t ^ 2 := by
    rw [lineEnergy]
    simp only [one_mul, hF]
  have hWaesm : MeasureTheory.AEStronglyMeasurable W
      (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have hcont : ContinuousOn W (Set.Ioc (1 : ℝ) T) := by
      rw [hW]
      refine ContinuousOn.log (by fun_prop) ?_
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht.1
      exact ne_of_gt (by positivity)
    exact hcont.aestronglyMeasurable measurableSet_Ioc
  have hWsq : MeasureTheory.Integrable
      (fun x : ℝ => W x ^ 2) (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have hii : IntervalIntegrable (fun t : ℝ => W t ^ 2) MeasureTheory.volume 1 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT, hW]
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.log (by fun_prop) ?_
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
      exact ne_of_gt (by positivity)
    simpa only [MeasureTheory.IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hii
  have hFaesm : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t => Real.sqrt (F t ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (by simpa only [hF] using
          hGsq.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self)
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    exact Real.sqrt_sq (norm_nonneg _)
  have hFmem : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hFaesm]
    simpa only [Real.norm_eq_abs, sq_abs, MeasureTheory.IntegrableOn] using hGsq.integrableOn
  have hWmem : MeasureTheory.MemLp W 2 (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hWaesm]
    simpa only [Real.norm_eq_abs, sq_abs] using hWsq
  have hCS := setIntegral_mul_le_sqrt hFmem hWmem
  have hmono : (∫ x in Set.Ioc (1 : ℝ) T, F x ^ 2) ≤ lineEnergy δ 1 := by
    rw [hline]
    refine MeasureTheory.setIntegral_mono_set hGsq.integrableOn ?_ ?_
    · filter_upwards with x using by positivity
    · filter_upwards with x hx using lt_trans one_pos hx.1
  simp only [intervalIntegral.integral_of_le hT]
  have hstep : (1 / (2 * π)) * (∫ x in Set.Ioc (1 : ℝ) T, F x * W x)
      ≤ (1 / (2 * π)) *
        (sqrt (lineEnergy δ 1) * sqrt (∫ x in Set.Ioc (1 : ℝ) T, W x ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hCS.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _))
  refine hstep.trans (le_of_eq ?_)
  ring_nf

/-! ### Private port of the derivative energy integrability of `Decomp389b`

`Decomp389b` proves that the squared derivative of `gaussianMellin δ` is integrable on the
critical line, but only through `private` lemmas, which a later module cannot name.  The block
below restates that development (same statements, same proofs) under private names of this
module, so that the leaf `error_weight_cauchy_schwarz` can use the derivative energy on the
whole half line `Ioi 1`.  Nothing outside this section depends on it. -/

section PortedDerivativeEnergy

open MeasureTheory Filter Asymptotics
open scoped FourierTransform

private lemma p_gauss_cont (δ : ℝ) :
    Continuous (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) := by
  unfold e
  fun_prop

private lemma p_gauss_isBigO_top (δ : ℝ) :
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

private lemma p_gauss_isBigO_bot (δ : ℝ) {b : ℝ} (hb : 0 < b) :
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

private lemma p_gauss_mellin_hasDerivAt (δ : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s) s := by
  have hfc : LocallyIntegrableOn (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
      (Set.Ioi 0) :=
    (p_gauss_cont δ).locallyIntegrable.locallyIntegrableOn _
  exact (mellin_hasDerivAt_of_isBigO_rpow hfc (p_gauss_isBigO_top δ) hs1
    (p_gauss_isBigO_bot δ (by linarith : (0:ℝ) < s.re / 2)) (by linarith)).2

private lemma p_weighted_cont (δ : ℝ) :
    Continuous (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  unfold e
  fun_prop

private lemma p_mellin_log_eq_fourier (δ t : ℝ) :
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

private lemma p_weighted_norm (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = |u| * (exp (u / 2) * exp (-(exp u) ^ 2 / 2)) := by
  rw [norm_mul, log_norm, Complex.norm_real, Real.norm_eq_abs]

private lemma p_weighted_norm_sq (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = u ^ 2 * (exp u * exp (-(exp u) ^ 2)) := by
  rw [p_weighted_norm, mul_pow, mul_pow, sq_abs]
  congr 1
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

private lemma p_weighted_le (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤
      4 * exp (-(1 / 4 : ℝ) * |u|) := by
  rw [p_weighted_norm]
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

private lemma p_weighted_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  refine Integrable.mono' ((integrable_exp_neg_abs_mul (c := 1 / 4) (by norm_num)).const_mul 4)
    (p_weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact p_weighted_le δ u

private lemma p_weighted_memLp (δ : ℝ) :
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
  refine MemLp.mono' hg (p_weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact p_weighted_le δ u

private lemma p_integrable_fourier_sq_weighted (δ : ℝ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) := by
  have h2 := p_weighted_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (p_weighted_integrable δ)
    (p_weighted_memLp δ)] with ξ hξ
  rw [hξ]

private lemma p_deriv_mellin_sq_pointwise (δ t : ℝ) :
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [(p_gauss_mellin_hasDerivAt δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num)).deriv, p_mellin_log_eq_fourier δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

private lemma p_integrable_deriv_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
      ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) hR).mpr
      (p_integrable_fourier_sq_weighted δ)
  refine h.congr ?_
  filter_upwards with t
  exact (p_deriv_mellin_sq_pointwise δ t).symm

end PortedDerivativeEnergy

/-- LEAF. Cauchy Schwarz on the height interval above height `1` against the derivative
energy: the integral of the derivative values against the shifted log weight is at most the
square root of the derivative energy times the square root of the squared shifted log weight
integral.  This leaf carries no character, zero or main term input. -/
theorem error_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) ≤
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set F : ℝ → ℝ :=
    fun t => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ with hF
  set W : ℝ → ℝ := fun t => 0.15 * log ((q : ℝ) * t) + 3.389 with hW
  show (∫ t in (1 : ℝ)..T, F t * W t) ≤
    sqrt (derivativeEnergy δ 1) * sqrt (∫ t in (1 : ℝ)..T, W t ^ 2)
  have hFsq : MeasureTheory.Integrable (fun t : ℝ => F t ^ 2) := by
    simpa only [hF] using p_integrable_deriv_mellin_sq δ
  have hde : derivativeEnergy δ 1 = ∫ t in Set.Ioi (1 : ℝ), F t ^ 2 := by
    rw [derivativeEnergy]
    simp only [one_mul, hF]
  have hWcont : ContinuousOn W (Set.Ici (1 : ℝ)) := by
    rw [hW]
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h1 : ContinuousAt (fun t : ℝ => log ((q : ℝ) * t)) t :=
      (Real.continuousAt_log (ne_of_gt (by positivity))).comp (by fun_prop)
    exact ((h1.const_mul 0.15).add continuousAt_const).continuousWithinAt
  have hWaesm : MeasureTheory.AEStronglyMeasurable W
      (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) :=
    (hWcont.mono (fun x hx => le_of_lt hx.1)).aestronglyMeasurable measurableSet_Ioc
  have hWsq : MeasureTheory.Integrable
      (fun x : ℝ => W x ^ 2) (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have hii : IntervalIntegrable (fun t : ℝ => W t ^ 2) MeasureTheory.volume 1 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      exact (hWcont.mono (fun x hx => hx.1)).pow 2
    simpa only [MeasureTheory.IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hii
  have hFaesm : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun t => Real.sqrt (F t ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (by simpa only [hF] using
          hFsq.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self)
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    exact Real.sqrt_sq (norm_nonneg _)
  have hFmem : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hFaesm]
    simpa only [Real.norm_eq_abs, sq_abs, MeasureTheory.IntegrableOn] using hFsq.integrableOn
  have hWmem : MeasureTheory.MemLp W 2 (MeasureTheory.volume.restrict (Set.Ioc (1 : ℝ) T)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hWaesm]
    simpa only [Real.norm_eq_abs, sq_abs, MeasureTheory.IntegrableOn] using hWsq
  have hCS := setIntegral_mul_le_sqrt hFmem hWmem
  have hmono : (∫ x in Set.Ioc (1 : ℝ) T, F x ^ 2) ≤ derivativeEnergy δ 1 := by
    rw [hde]
    refine MeasureTheory.setIntegral_mono_set hFsq.integrableOn ?_ ?_
    · filter_upwards with x using by positivity
    · filter_upwards with x hx using hx.1
  simp only [intervalIntegral.integral_of_le hT]
  exact hCS.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _))

/-- The positive signed zero sampling inequality, assembled from the four leaves: sign
removal, zero sum to line integral, and the two interval Cauchy Schwarz estimates. -/
theorem positive_sampling_raw_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    positiveMass χ δ T ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  have h1 := positive_mass_le_norm_sum q χ δ T
  have h2 := positive_mass_norm_sum_integral q χ hχ δ T hT hlarge hzeros
  have h3 := main_weight_cauchy_schwarz q δ T hT
  have h4 := error_weight_cauchy_schwarz q δ T hT
  exact h1.trans (h2.trans (add_le_add (add_le_add h3 h4) le_rfl))

end LeanLab.HelfgottMajor.Decomp431a
