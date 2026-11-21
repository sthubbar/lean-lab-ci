import LeanLab.HelfgottMajor.MainTail123

/-!
PREP session 2026-11-21, splitter HM-tail. P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897v4, Lemma 4.5, page 41, displays 4.33 to 4.35, with Lemma 4.3, page 38,
displays 4.26 to 4.28. Route step `MainTail123.tail_mass_bound_leaf`.

REPAIR ROUTE. The printed proof of the bound half has two gaps, recorded as a QUESTION in
notes/burst-20261120c/tail.md:
1. after display 4.28, page 38 drops the boundary term f(y) g(y) of the partial summation;
2. the pairing of ρ with 1 - ρ in the first display of the proof of Lemma 4.5 needs χ real.

This file gives a corrected route that uses neither. It sums over both signs of the ordinate
with the two sided count of display 4.26, taken from hB, and it keeps the boundary term of the
partial summation. The price is a factor 2 on the integral of display 4.35 and an explicit
boundary term `4 · 4.226 · G(T) · bookError q T`. So the final theorem proves a REPAIRED bound,
`tail_mass_bound_repaired`, and NOT the sealed statement of `tail_mass_bound_leaf`, which is
left unchanged and open. Whether the sealed bound itself holds for complex χ stays a QUESTION:
from hcor and hB alone the route below is the best this partial summation gives.

The repaired route, with G the majorant `tailEnv` of display 4.34 and g = - G', every step
PROVED in this file, the whole CONDITIONAL ON hB and hcor only:
  sum of mellinMassTerm ≤ 4.226 · Σ mult · G(|γ|)          mass_le_tailEnv, from hcor
                       = 4.226 · Σ mult · ∫_{|γ|}^∞ g        tailEnv_eq_integral
                       ≤ 4.226 · ∫_T^∞ g(t) U(t) dt          layer_cake_le, by finite sums
  with U(t) = 2 (M(t) - M(T)) + 2 (E(t) + E(T)), M = bookMain, E = bookError, from hB by
  count_increment_le, and
  ∫ g (M - M(T)) = ∫ G M'                                    ibp_main
  ∫ g E = G(T) E(T) + ∫ G E'                                 ibp_error, boundary term KEPT
  ∫ G M' + ∫ G E' ≤ ∫ G · countDensity = expTail + gaussTail density_integral_le and
                                                             tailEnv_integral_split.
Every step is proved here; the LEAF cut of the first draft closed in this session.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121TailRepair
open Real MeasureTheory Filter Topology LeanLab.HelfgottArcs
open LeanLab.HelfgottMajor.SplitGaussian123

/-- The majorant of display 4.34, page 41, without the factor 4.226, written as a sum of its
two branches so that it is smooth: by `SplitGaussian123.corEnvelope_le` it dominates the
envelope of Corollary 3.2. The Gaussian branch is absent at zero shift. -/
noncomputable def tailEnv (δ t : ℝ) : ℝ :=
  exp (-0.1598 * t) + if δ = 0 then 0 else exp (-0.1065 * (t / (π * |δ|)) ^ 2)

/-- Minus the derivative of `tailEnv`, the weight - f' of displays 4.27 and 4.28, page 38. -/
noncomputable def tailEnvDeriv (δ t : ℝ) : ℝ :=
  0.1598 * exp (-0.1598 * t) + if δ = 0 then 0 else
    2 * 0.1065 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2)

/-- The two sided zero count N(t, χ) of display 4.26, page 38: zeros in the open strip with
absolute ordinate at most t, with multiplicity. -/
noncomputable def twoSidedCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ t).toFinset, (ZeroCount1623.mult χ ρ : ℝ)

/-- The index type of the zeros above height T, as in `MainTail123.tail_mass_bound_leaf`. -/
abbrev TailIdx {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Type :=
  {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}

/-- The main density M'(t) of display 4.28, page 38: the derivative of `bookMain q t`. -/
noncomputable def mainDensity (q : ℕ) (t : ℝ) : ℝ := 1 / (2 * π) * log ((q : ℝ) * t / (2 * π))

/-! ## Proved pieces -/

/-- PROVED. P0014 page 41, display 4.33 without the pairing: by Corollary 3.2 at k equal to 0,
given as hcor, one zero's Mellin mass is at most 4.226 times its multiplicity times the
majorant of display 4.34. Only the term at ρ is used, so χ need not be real. -/
theorem mass_le_tailEnv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (ρ : TailIdx χ T) :
    mellinMassTerm χ δ ρ.val ≤
      4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) * tailEnv δ |ρ.val.im|) := by
  have h1 := zero_mass_le_envelope χ δ T hT hcor ρ
  have h2 := mul_le_mul_of_nonneg_left (corEnvelope_le δ ρ.val.im)
    (show (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * 4.226
      by positivity)
  have e : tailEnv δ |ρ.val.im| = exp (-0.1598 * |ρ.val.im|) +
      if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := by
    rfl
  rw [e]
  calc mellinMassTerm χ δ ρ.val ≤ _ := h1
    _ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * 4.226 *
          corEnvelope δ ρ.val.im := by ring
    _ ≤ _ := h2
    _ = _ := by ring

/-- PROVED. The weight - f' is nonnegative for t at least 0, so f of display 4.34 decreases. -/
theorem tailEnvDeriv_nonneg (δ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tailEnvDeriv δ t := by
  unfold tailEnvDeriv
  split_ifs
  · positivity
  · positivity

/-- PROVED, CONDITIONAL ON hB, the cited count of display 4.26, page 38. The increment of the
two sided count between heights T and t, with BOTH error terms kept: this is where the
boundary term of display 4.27 comes from. -/
theorem count_increment_le (hB : MainHyps123.BookZeroCount) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T t : ℝ} (hT : 1 ≤ T) (hTt : T ≤ t) :
    twoSidedCount χ t - twoSidedCount χ T ≤
      2 * (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) +
        2 * (ZeroCount1623.bookError q t + ZeroCount1623.bookError q T) := by
  have h1 := abs_le.mp (MainTail123.zero_count_two_sided_of_book hB χ hχ (hT.trans hTt))
  have h2 := abs_le.mp (MainTail123.zero_count_two_sided_of_book hB χ hχ hT)
  unfold twoSidedCount
  linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Analytic helpers, all PROVED -/

/-- PROVED. The majorant of display 4.34 is nonnegative. -/
theorem tailEnv_nonneg (δ t : ℝ) : 0 ≤ tailEnv δ t := by
  unfold tailEnv; split_ifs <;> positivity

/-- PROVED. The majorant of display 4.34 is continuous. -/
theorem continuous_tailEnv (δ : ℝ) : Continuous (tailEnv δ) := by
  unfold tailEnv; split_ifs <;> fun_prop

/-- PROVED. The weight - f' is continuous. -/
theorem continuous_tailEnvDeriv (δ : ℝ) : Continuous (tailEnvDeriv δ) := by
  unfold tailEnvDeriv; split_ifs <;> fun_prop


/-- PROVED. The derivative of - f is the weight - f', page 41, display 4.34. -/
theorem hasDerivAt_neg_tailEnv (δ x : ℝ) :
    HasDerivAt (fun t => -tailEnv δ t) (tailEnvDeriv δ x) x := by
  have h1 : HasDerivAt (fun t : ℝ => exp (-0.1598 * t)) (exp (-0.1598 * x) * (-0.1598)) x := by
    simpa using ((hasDerivAt_id x).const_mul (-0.1598 : ℝ)).exp
  by_cases hδ : δ = 0
  · simp only [tailEnv, tailEnvDeriv, hδ, ite_true, add_zero]
    convert h1.neg using 1; ring
  · simp only [tailEnv, tailEnvDeriv, hδ, ite_false]
    set a := π * |δ|
    have h2 : HasDerivAt (fun t : ℝ => exp (-0.1065 * (t / a) ^ 2))
        (exp (-0.1065 * (x / a) ^ 2) * (-0.1065 * (2 * (x / a) ^ 1 * (1 / a)))) x := by
      have hd : HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
        simpa using (hasDerivAt_id x).div_const a
      exact ((hd.pow 2).const_mul (-0.1065 : ℝ)).exp
    convert (h1.add h2).neg using 1
    ring

/-- PROVED. f of display 4.34 tends to 0, as used on page 38. -/
theorem tendsto_neg_tailEnv (δ : ℝ) : Tendsto (fun t => -tailEnv δ t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => exp (-0.1598 * t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have h2 : Tendsto (fun t : ℝ => if δ = 0 then (0:ℝ) else exp (-0.1065 * (t / (π * |δ|)) ^ 2))
      atTop (𝓝 0) := by
    by_cases hδ : δ = 0
    · simp [hδ]
    · simp only [hδ, ite_false]
      have ha : 0 < π * |δ| := by positivity
      apply tendsto_exp_atBot.comp
      apply Tendsto.const_mul_atTop_of_neg (by norm_num)
      exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_id.atTop_div_const ha)
  simpa [tailEnv] using (h1.add h2).neg

/-- PROVED. t cubed times the majorant is integrable on the tail. -/
theorem integrableOn_cube_tailEnv (δ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t => t ^ (3 : ℝ) * tailEnv δ t) (Set.Ioi T) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (3 : ℝ) * exp (-0.1598 * t)) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 3) (p := 1) (b := 0.1598)
      (by norm_num) one_pos (by norm_num)
    simpa only [rpow_one] using this
  have h1' := h1.mono_set (Set.Ioi_subset_Ioi hT)
  by_cases hd : δ = 0
  · refine h1'.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [tailEnv, hd]
  · have ha : 0 < π * |δ| := by have := abs_pos.mpr hd; positivity
    have h2 : IntegrableOn (fun t : ℝ => t ^ (3 : ℝ) *
        exp (-(0.1065 / (π * |δ|) ^ 2) * t ^ (2 : ℝ))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) two_pos (by positivity)
    refine (h1'.add (h2.mono_set (Set.Ioi_subset_Ioi hT))).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp only [Pi.add_apply, tailEnv, hd, ite_false, rpow_two]
    rw [div_pow]; ring_nf

/-- PROVED. The weight - f' is at most a constant times t times f, for t at least 1. -/
theorem tailEnvDeriv_le (δ : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    tailEnvDeriv δ t ≤ (1 + 2 * 0.1065 / (π * |δ|) ^ 2) * t * tailEnv δ t := by
  unfold tailEnvDeriv tailEnv
  have e1 := exp_pos (-0.1598 * t)
  by_cases hd : δ = 0
  · simp only [hd, ite_true, add_zero, abs_zero, mul_zero]
    simp
    have e1' := exp_pos (-(0.1598 * t))
    nlinarith
  · simp only [hd, ite_false]
    have ha : 0 < π * |δ| := by have := abs_pos.mpr hd; positivity
    have e2 := exp_pos (-0.1065 * (t / (π * |δ|)) ^ 2)
    have hk : 0 ≤ 2 * 0.1065 / (π * |δ|) ^ 2 := by positivity
    have : 2 * 0.1065 * t / (π * |δ|) ^ 2 = 2 * 0.1065 / (π * |δ|) ^ 2 * t := by ring
    rw [this]
    nlinarith [mul_nonneg hk e1.le, mul_nonneg (mul_nonneg hk (by linarith : (0:ℝ) ≤ t)) e1.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) e2.le, mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) e1.le]

/-- PROVED. Integrability on the tail of f and - f' against any continuous function of at most
quadratic growth, for the integrals of displays 4.27, 4.28 and 4.35. -/
theorem integrable_env_mul (δ : ℝ) {T C : ℝ} (hT : 1 ≤ T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici T)) (hb : ∀ t, T ≤ t → |f t| ≤ C * t ^ 2) :
    IntegrableOn (fun t => tailEnv δ t * f t) (Set.Ioi T) ∧
      IntegrableOn (fun t => tailEnvDeriv δ t * f t) (Set.Ioi T) := by
  set K := 1 + 2 * 0.1065 / (π * |δ|) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hdom := integrableOn_cube_tailEnv δ (by linarith : (0:ℝ) ≤ T)
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioi T)) :=
    (hf.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hcube : ∀ t, T ≤ t → t ^ 2 ≤ t ^ (3 : ℝ) := by
    intro t ht
    have h1 : (1:ℝ) ≤ t := hT.trans ht
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]
    nlinarith
  have hC : ∀ t, T ≤ t → |f t| ≤ |C| * t ^ (3 : ℝ) := fun t ht =>
    (hb t ht).trans (mul_le_mul (le_abs_self C) (hcube t ht) (by positivity) (abs_nonneg C))
  constructor
  · refine Integrable.mono' (hdom.const_mul (|C|)) ((continuous_tailEnv δ).aestronglyMeasurable.mul hfm) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have h := hC t (le_of_lt ht)
    rw [norm_mul, Real.norm_of_nonneg (tailEnv_nonneg δ t), Real.norm_eq_abs]
    have := tailEnv_nonneg δ t
    nlinarith
  · refine Integrable.mono' ((hdom.const_mul (|C|)).const_mul K)
      ((continuous_tailEnvDeriv δ).aestronglyMeasurable.mul hfm) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht1 : (1:ℝ) ≤ t := hT.trans (le_of_lt ht)
    have h := hC t (le_of_lt ht)
    have hd0 : 0 ≤ tailEnvDeriv δ t := by
      unfold tailEnvDeriv; split_ifs <;> positivity
    have hdl := tailEnvDeriv_le δ ht1
    rw [norm_mul, Real.norm_of_nonneg hd0, Real.norm_eq_abs]
    have := tailEnv_nonneg δ t
    have hf2 : |f t| ≤ |C| * t ^ 2 :=
      (hb t (le_of_lt ht)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have h3 : t ^ (3:ℝ) = t * t ^ 2 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]; ring
    calc tailEnvDeriv δ t * |f t| ≤ (K * t * tailEnv δ t) * (|C| * t ^ 2) :=
          mul_le_mul hdl hf2 (abs_nonneg _) (by positivity)
      _ = _ := by rw [h3]; ring

/-- PROVED. An elementary two sided bound on the logarithm. -/
theorem abs_log_le_add_inv {y : ℝ} (hy : 0 < y) : |log y| ≤ y + y⁻¹ := by
  have h1 := log_le_sub_one_of_pos hy
  have h2 := log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [log_inv] at h2
  have := inv_pos.mpr hy
  rw [abs_le]; constructor <;> linarith

/-- PROVED. Quadratic growth bound for the main density. -/
theorem mainDensity_bound (q : ℕ) [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    |mainDensity q t| ≤ ((q : ℝ) + 7) * t ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hy : 0 < (q : ℝ) * t / (2 * π) := by positivity
  have hl := abs_log_le_add_inv hy
  have hpi := pi_gt_three
  have h1 : (q : ℝ) * t / (2 * π) ≤ q * t := div_le_self (by positivity) (by linarith)
  have h2 : ((q : ℝ) * t / (2 * π))⁻¹ ≤ 7 := by
    rw [inv_div, div_le_iff₀ (by positivity)]
    have hqt : (1:ℝ) ≤ q * t := by nlinarith
    nlinarith [pi_lt_d2]
  unfold mainDensity
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  have h3 : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  calc 1 / (2 * π) * |log ((q : ℝ) * t / (2 * π))| ≤ 1 * (q * t + 7) := by
        apply mul_le_mul h3 (by linarith) (abs_nonneg _) (by norm_num)
    _ ≤ _ := by nlinarith

/-- PROVED. Quadratic growth bound for the density of display 4.35. -/
theorem countDensity_bound (q : ℕ) [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    |TailIntegral123.countDensity q t| ≤ ((q : ℝ) + 8) * t ^ 2 := by
  have h := mainDensity_bound q ht
  have e : TailIntegral123.countDensity q t = mainDensity q t + 1 / (4 * t) := rfl
  have h4 : |1 / (4 * t)| ≤ t ^ 2 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]; nlinarith
  rw [e]; calc _ ≤ |mainDensity q t| + |1 / (4 * t)| := abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- PROVED. Quadratic growth bound for the error of display 4.26. -/
theorem bookError_bound (q : ℕ) [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    |ZeroCount1623.bookError q t| ≤ ((q : ℝ) + 4) * t ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqt : (1:ℝ) ≤ q * t := by nlinarith
  have hl0 := log_nonneg hqt
  have hl := log_le_sub_one_of_pos (by linarith : (0:ℝ) < q * t)
  unfold ZeroCount1623.bookError
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-- PROVED. Quadratic growth bound for the main term of display 4.26. -/
theorem bookMain_bound (q : ℕ) [NeZero q] {t : ℝ} (ht : 1 ≤ t) :
    |ZeroCount1623.bookMain q t| ≤ ((q : ℝ) + 18) * t ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hpi := pi_gt_three
  have he : exp 1 < 2.7182818286 := exp_one_lt_d9
  have hy : 0 < (q : ℝ) * t / (2 * π * exp 1) := by positivity
  have hl := abs_log_le_add_inv hy
  have h1 : (q : ℝ) * t / (2 * π * exp 1) ≤ q * t :=
    div_le_self (by positivity) (by nlinarith [add_one_le_exp (1:ℝ)])
  have hqt : (1:ℝ) ≤ q * t := by nlinarith
  have h2 : ((q : ℝ) * t / (2 * π * exp 1))⁻¹ ≤ 18 := by
    rw [inv_div, div_le_iff₀ (by positivity)]
    nlinarith [pi_lt_d2, exp_pos 1]
  unfold ZeroCount1623.bookMain
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < t / (2 * π))]
  have h3 : t / (2 * π) ≤ t := div_le_self (by linarith) (by linarith)
  calc t / (2 * π) * |log ((q : ℝ) * t / (2 * π * exp 1))| ≤ t * (q * t + 18) := by
        apply mul_le_mul h3 (by linarith) (abs_nonneg _) (by linarith)
    _ ≤ _ := by nlinarith

/-- PROVED. Continuity of the density of display 4.35 on the tail. -/
theorem continuousOn_countDensity (q : ℕ) [NeZero q] {T : ℝ} (hT : 1 ≤ T) :
    ContinuousOn (fun t => TailIntegral123.countDensity q t) (Set.Ici T) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  unfold TailIntegral123.countDensity
  apply ContinuousOn.add
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; positivity
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; positivity

/-- PROVED. Continuity of the main term of display 4.26 on the tail. -/
theorem continuousOn_bookMain (q : ℕ) [NeZero q] {T : ℝ} (hT : 1 ≤ T) :
    ContinuousOn (fun t => ZeroCount1623.bookMain q t) (Set.Ici T) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  unfold ZeroCount1623.bookMain
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.log (by fun_prop)
  intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; positivity

/-- PROVED. Continuity of the error of display 4.26 on the tail. -/
theorem continuousOn_bookError (q : ℕ) [NeZero q] {T : ℝ} (hT : 1 ≤ T) :
    ContinuousOn (fun t => ZeroCount1623.bookError q t) (Set.Ici T) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  unfold ZeroCount1623.bookError
  apply ContinuousOn.add _ continuousOn_const
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; positivity

/-! ## Leaves and the pieces proved from them -/

/-- PROVED. P0014 page 41, display 4.34 and the sentence after it, f decreasing with limit 0,
as used in the partial summation of page 38 before display 4.26: the majorant is the integral
of its weight - f' from a to infinity, for a at least 0. -/
theorem tailEnv_eq_integral (δ : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (tailEnvDeriv δ) (Set.Ioi a) ∧
      tailEnv δ a = ∫ t in Set.Ioi a, tailEnvDeriv δ t := by
  have hc : ContinuousWithinAt (fun t => -tailEnv δ t) (Set.Ici a) a :=
    (hasDerivAt_neg_tailEnv δ a).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Set.Ioi a, HasDerivAt (fun t => -tailEnv δ t) (tailEnvDeriv δ x) x :=
    fun x _ => hasDerivAt_neg_tailEnv δ x
  have hp : ∀ x ∈ Set.Ioi a, 0 ≤ tailEnvDeriv δ x :=
    fun x hx => tailEnvDeriv_nonneg δ (ha.trans (le_of_lt hx))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp (tendsto_neg_tailEnv δ), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp (tendsto_neg_tailEnv δ)]
  ring

/-- A finite piece of the count N(t, χ) of display 4.26, page 38: the zeros of a finite set S
of zeros above T with ordinate below t, with multiplicity. Used only to cut the Stieltjes step of
page 38 into finite sums. -/
noncomputable def finCount {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {T : ℝ}
    (S : Finset (TailIdx χ T)) (t : ℝ) : ℝ :=
  ∑ ρ ∈ S, if |ρ.val.im| < t then (ZeroCount1623.mult χ ρ.val : ℝ) else 0

/-- PROVED. A finite piece of the count increment is at most the full increment of display 4.26. -/
theorem finCount_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (S : Finset (TailIdx χ T)) {t : ℝ} (ht : T < t) :
    finCount S t ≤ twoSidedCount χ t - twoSidedCount χ T := by
  classical
  set A := (ZeroCount1623.stripZeros_finite χ t).toFinset
  set B := (ZeroCount1623.stripZeros_finite χ T).toFinset
  have hBA : B ⊆ A := by
    intro z hz
    simp only [A, B, Set.Finite.mem_toFinset, ZeroCount1623.stripZeros] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans ht.le⟩
  have hdiff : twoSidedCount χ t - twoSidedCount χ T =
      ∑ z ∈ A \ B, (ZeroCount1623.mult χ z : ℝ) := by
    unfold twoSidedCount
    rw [← Finset.sum_sdiff hBA]; ring
  rw [hdiff]
  unfold finCount
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun ρ : TailIdx χ T => ρ.val) ↑(S.filter fun ρ => |ρ.val.im| < t) :=
    fun a _ b _ h => Subtype.ext h
  rw [← Finset.sum_image (f := fun z => (ZeroCount1623.mult χ z : ℝ)) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_filter] at hz
    obtain ⟨ρ, ⟨_, hρt⟩, rfl⟩ := hz
    simp only [A, B, Finset.mem_sdiff, Set.Finite.mem_toFinset, ZeroCount1623.stripZeros]
    refine ⟨⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, hρt.le⟩, ?_⟩
    intro h; exact absurd h.2.2.2 (not_le.mpr ρ.property.2.2.2)
  · intro _ _ _; positivity

/-- PROVED. The finite Stieltjes swap of page 38: a finite sum of tail integrals of g is the
integral of g against the finite count. -/
theorem finCount_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (g : ℝ → ℝ) (hgint : IntegrableOn g (Set.Ioi T)) (S : Finset (TailIdx χ T)) :
    ∑ ρ ∈ S, (ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, g t =
      ∫ t in Set.Ioi T, g t * finCount S t := by
  classical
  have hterm : ∀ ρ : TailIdx χ T, (fun t => g t *
      (if |ρ.val.im| < t then (ZeroCount1623.mult χ ρ.val : ℝ) else 0)) =
      fun t => (ZeroCount1623.mult χ ρ.val : ℝ) * (Set.Ioi |ρ.val.im|).indicator g t := by
    intro ρ; funext t
    by_cases h : |ρ.val.im| < t
    · simp [h]; ring
    · simp [h]
  have hint : ∀ ρ ∈ S, Integrable (fun t => g t *
      (if |ρ.val.im| < t then (ZeroCount1623.mult χ ρ.val : ℝ) else 0))
      (volume.restrict (Set.Ioi T)) := by
    intro ρ _
    rw [hterm ρ]
    exact (hgint.indicator measurableSet_Ioi).const_mul _
  unfold finCount
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum S hint]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [hterm ρ, integral_const_mul, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi ρ.property.2.2.2.le)]

/-- PROVED from `finCount_le` and `finCount_integral`. P0014 page 38, the first display of the proof of Lemma 4.3, the Stieltjes rewriting
of a sum over zeros above y as an integral of - f' against the count, here two sided and as an
inequality against any upper bound U of the count increment. -/
theorem layer_cake_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (g U : ℝ → ℝ) (hg : ∀ t, T < t → 0 ≤ g t) (hgint : IntegrableOn g (Set.Ioi T))
    (hU : ∀ t, T < t → twoSidedCount χ t - twoSidedCount χ T ≤ U t)
    (hgU : IntegrableOn (fun t => g t * U t) (Set.Ioi T)) :
    Summable (fun ρ : TailIdx χ T =>
        (ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, g t) ∧
      (∑' ρ : TailIdx χ T,
        (ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, g t) ≤
        ∫ t in Set.Ioi T, g t * U t := by
  have hnn : 0 ≤ fun ρ : TailIdx χ T =>
      (ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, g t := by
    intro ρ
    apply mul_nonneg (Nat.cast_nonneg _)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact hg t (ρ.property.2.2.2.trans ht)
  have hfin : ∀ S : Finset (TailIdx χ T), ∑ ρ ∈ S,
      (ZeroCount1623.mult χ ρ.val : ℝ) * (∫ t in Set.Ioi |ρ.val.im|, g t) ≤
        ∫ t in Set.Ioi T, g t * U t := by
    intro S
    rw [finCount_integral χ g hgint S]
    apply integral_mono_of_nonneg
    · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
      apply mul_nonneg (hg t ht)
      unfold finCount
      apply Finset.sum_nonneg; intro _ _; split_ifs <;> positivity
    · exact hgU
    · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
      exact mul_le_mul_of_nonneg_left ((finCount_le χ S ht).trans (hU t ht)) (hg t ht)
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- PROVED from `integrable_env_mul`. P0014 page 38, displays 4.27 and 4.28, integrability: - f' times the main increment
and - f' times the error are integrable on the tail, since f decays exponentially and the count
terms grow like t log t. -/
theorem ibp_integrable (q : ℕ) [NeZero q] (δ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn (fun t => tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T)) (Set.Ioi T) ∧
      IntegrableOn (fun t => tailEnvDeriv δ t * ZeroCount1623.bookError q t) (Set.Ioi T) := by
  refine ⟨(integrable_env_mul δ hT _ ((continuousOn_bookMain q hT).sub continuousOn_const)
    (C := (q : ℝ) + 18 + |ZeroCount1623.bookMain q T|) ?_).2,
    (integrable_env_mul δ hT _ (continuousOn_bookError q hT) (fun t ht =>
      bookError_bound q (hT.trans ht))).2⟩
  intro t ht
  have h1 := bookMain_bound q (hT.trans ht)
  have ht2 : (1:ℝ) ≤ t ^ 2 := by nlinarith
  calc |ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T| ≤ |ZeroCount1623.bookMain q t| + |ZeroCount1623.bookMain q T| := abs_sub _ _
    _ ≤ _ := by nlinarith [abs_nonneg (ZeroCount1623.bookMain q T)]

/-- PROVED from `integrable_env_mul`. P0014 page 41, display 4.35: the corrected density M'(t) + 0.15 / t is at most the
density 1 / 2π log(qt / 2π) + 1 / 4t of display 4.35, integrated against f. -/
theorem density_integral_le (q : ℕ) [NeZero q] (δ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Ioi T, tailEnv δ t * mainDensity q t) +
        (∫ t in Set.Ioi T, tailEnv δ t * (0.15 / t)) ≤
      ∫ t in Set.Ioi T, tailEnv δ t * TailIntegral123.countDensity q t := by
  have h1 := (integrable_env_mul δ hT _ (C := (q : ℝ) + 7) (by
    unfold mainDensity
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    have : (1:ℝ) ≤ t := hT.trans ht
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity) (fun t ht => mainDensity_bound q (hT.trans ht))).1
  have h2 := (integrable_env_mul δ hT (fun t => 0.15 / t) (C := 1) (by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; simp only [id]; positivity) (by
    intro t ht
    have : (1:ℝ) ≤ t := hT.trans ht
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]; nlinarith)).1
  have h3 := (integrable_env_mul δ hT _ (continuousOn_countDensity q hT)
    (fun t ht => countDensity_bound q (hT.trans ht))).1
  rw [← integral_add h1 h2]
  apply setIntegral_mono_on (h1.add h2) h3 measurableSet_Ioi
  intro t ht
  have ht1 : (1:ℝ) ≤ t := hT.trans (le_of_lt ht)
  have hG : 0 ≤ tailEnv δ t := by unfold tailEnv; split_ifs <;> positivity
  have e : TailIntegral123.countDensity q t = mainDensity q t + 1 / (4 * t) := rfl
  rw [e]
  have : 0.15 / t ≤ 1 / (4 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left this hG]

/-- PROVED from `integrable_env_mul`. P0014 page 41, displays 4.35 and 4.36 to 4.41: the integral of display 4.35 splits
into the exponential integral and the Gaussian integral, the latter absent at zero shift. -/
theorem tailEnv_integral_split (q : ℕ) [NeZero q] (δ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Ioi T, tailEnv δ t * TailIntegral123.countDensity q t) =
      TailIntegral123.expTailIntegral q T + TailIntegral123.gaussianTailIntegral q δ T := by
  have hb : ∀ t, T ≤ t → |TailIntegral123.countDensity q t| ≤ ((q : ℝ) + 8) * t ^ 2 :=
    fun t ht => countDensity_bound q (hT.trans ht)
  have h0 := (integrable_env_mul 0 hT _ (continuousOn_countDensity q hT) hb).1
  have hδ := (integrable_env_mul δ hT _ (continuousOn_countDensity q hT) hb).1
  have e0 : (fun t => tailEnv 0 t * TailIntegral123.countDensity q t) =
      fun t => exp (-0.1598 * t) * TailIntegral123.countDensity q t := by
    funext t; simp [tailEnv]
  rw [e0] at h0
  unfold TailIntegral123.expTailIntegral TailIntegral123.gaussianTailIntegral
  by_cases hd : δ = 0
  · subst hd; simp [tailEnv]
  · simp only [hd, ite_false]
    have e : (fun t => tailEnv δ t * TailIntegral123.countDensity q t) = fun t =>
        exp (-0.1598 * t) * TailIntegral123.countDensity q t +
          exp (-0.1065 * (t / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q t := by
      funext t; simp only [tailEnv, hd, ite_false]; ring
    have hg : IntegrableOn (fun t => exp (-0.1065 * (t / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q t)
        (Set.Ioi T) := by
      have := hδ.sub h0
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, tailEnv, hd, ite_false]; ring
    rw [e, integral_add h0 hg]

/-- PROVED. f of display 4.34 times a function of quadratic growth tends to 0, the vanishing
boundary term at infinity of the partial summation on page 38. -/
theorem tendsto_tailEnv_mul (δ : ℝ) {T C : ℝ} (f : ℝ → ℝ)
    (hb : ∀ t, T ≤ t → |f t| ≤ C * t ^ 2) :
    Tendsto (fun t => tailEnv δ t * f t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ 2 * exp (-0.1598 * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 0.1598 (by norm_num)
    simpa [rpow_two] using this
  have hE : Tendsto (fun t : ℝ => t ^ 2 * tailEnv δ t) atTop (𝓝 0) := by
    by_cases hd : δ = 0
    · simpa [tailEnv, hd] using h1
    · have ha : 0 < π * |δ| := by have := abs_pos.mpr hd; positivity
      have hb' : 0 < 0.1065 / (π * |δ|) ^ 2 := by positivity
      have h2 : Tendsto (fun t : ℝ => t ^ 2 * exp (-(0.1065 / (π * |δ|) ^ 2) * t ^ 2))
          atTop (𝓝 0) := by
        have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hb').comp
          (tendsto_pow_atTop (α := ℝ) two_ne_zero)
        simpa [Function.comp_def, rpow_one] using this
      have e : (fun t : ℝ => t ^ 2 * tailEnv δ t) = fun t =>
          t ^ 2 * exp (-0.1598 * t) + t ^ 2 * exp (-(0.1065 / (π * |δ|) ^ 2) * t ^ 2) := by
        funext t
        have : -0.1065 * (t / (π * |δ|)) ^ 2 = -(0.1065 / (π * |δ|) ^ 2) * t ^ 2 := by ring
        simp only [tailEnv, hd, ite_false, this]; ring
      rw [e]; simpa using h1.add h2
  apply squeeze_zero_norm' _ (by simpa using hE.const_mul |C|)
  filter_upwards [eventually_ge_atTop T] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tailEnv_nonneg δ t)]
  have h := (hb t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have := tailEnv_nonneg δ t
  calc tailEnv δ t * |f t| ≤ tailEnv δ t * (|C| * t ^ 2) := mul_le_mul_of_nonneg_left h this
    _ = _ := by ring

/-- PROVED. The derivative of the error `bookError q t` is 0.15 / t. -/
theorem hasDerivAt_bookError (q : ℕ) [NeZero q] {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => ZeroCount1623.bookError q t) (0.15 / x) x := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h := (((hasDerivAt_id x).const_mul (q : ℝ)).log
    (by simpa using (mul_pos hq hx).ne')).const_mul
    (0.15 : ℝ) |>.add_const (3.389 : ℝ)
  unfold ZeroCount1623.bookError
  simp only [id_eq, mul_one] at h
  convert h using 1
  rw [div_mul_cancel_left₀ hq.ne']
  ring

/-- PROVED. The derivative of the main term of display 4.26 is the density of display 4.28. -/
theorem hasDerivAt_bookMain (q : ℕ) [NeZero q] {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => ZeroCount1623.bookMain q t) (mainDensity q x) x := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hc : (0 : ℝ) < 2 * π * exp 1 := by positivity
  have hl : HasDerivAt (fun t => log ((q : ℝ) * t / (2 * π * exp 1)))
      (((q : ℝ) * 1 / (2 * π * exp 1)) / ((q : ℝ) * x / (2 * π * exp 1))) x :=
    (((hasDerivAt_id x).const_mul (q : ℝ)).div_const _).log
      (by simpa using (div_pos (mul_pos hq hx) hc).ne')
  have hm : HasDerivAt (fun t => t / (2 * π)) (1 / (2 * π)) x := by
    simpa using (hasDerivAt_id x).div_const (2 * π)
  have h := hm.mul hl
  unfold ZeroCount1623.bookMain
  convert h using 1
  have e : log ((q : ℝ) * x / (2 * π)) = log ((q : ℝ) * x / (2 * π * exp 1)) + 1 := by
    rw [show (q : ℝ) * x / (2 * π * exp 1) = (q : ℝ) * x / (2 * π) / exp 1 by ring,
      log_div (by positivity) (exp_pos 1).ne', log_exp]; ring
  unfold mainDensity
  rw [e]
  field_simp

/-- PROVED. P0014 page 38, display 4.28, corrected: integration by parts of - f' against the
main term increment M(t) - M(T). The boundary term vanishes at T, since the increment is 0
there, and at infinity, since f M tends to 0. -/
theorem ibp_main (q : ℕ) [NeZero q] (δ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Set.Ioi T, tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) =
      ∫ t in Set.Ioi T, tailEnv δ t * mainDensity q t := by
  have hT0 : 0 < T := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hu : ∀ x ∈ Set.Ioi T, HasDerivAt (fun t => -tailEnv δ t) (tailEnvDeriv δ x) x :=
    fun x _ => hasDerivAt_neg_tailEnv δ x
  have hv : ∀ x ∈ Set.Ioi T, HasDerivAt
      (fun t => ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) (mainDensity q x) x :=
    fun x hx => (hasDerivAt_bookMain q (hT0.trans hx)).sub_const _
  have hcm : ContinuousOn (fun t => mainDensity q t) (Set.Ici T) := by
    unfold mainDensity
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    have : (1:ℝ) ≤ t := hT.trans ht
    positivity
  have huv' : IntegrableOn ((fun t => -tailEnv δ t) * fun t => mainDensity q t)
      (Set.Ioi T) := by
    have := ((integrable_env_mul δ hT _ hcm
      (fun t ht => mainDensity_bound q (hT.trans ht))).1).neg
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp
  have hu'v : IntegrableOn (tailEnvDeriv δ * fun t =>
      ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) (Set.Ioi T) :=
    (ibp_integrable q δ hT).1
  have hcont : ContinuousAt (fun t => -tailEnv δ t *
      (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T)) T :=
    (continuous_tailEnv δ).neg.continuousAt.mul
      ((hasDerivAt_bookMain q hT0).continuousAt.sub continuousAt_const)
  have h_zero : Tendsto ((fun t => -tailEnv δ t) * fun t =>
      ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) (𝓝[>] T) (𝓝 0) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi T))
    simpa [Pi.mul_def] using this
  have h_infty : Tendsto ((fun t => -tailEnv δ t) * fun t =>
      ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) atTop (𝓝 0) := by
    have := (tendsto_tailEnv_mul δ (C := (q : ℝ) + 18 + |ZeroCount1623.bookMain q T|) _
      (fun t ht => by
        have h1 := bookMain_bound q (hT.trans ht)
        have ht2 : (1:ℝ) ≤ t ^ 2 := by nlinarith [hT.trans ht]
        calc |ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T|
            ≤ |ZeroCount1623.bookMain q t| + |ZeroCount1623.bookMain q T| := abs_sub _ _
          _ ≤ _ := by nlinarith [abs_nonneg (ZeroCount1623.bookMain q T)])).neg
    simpa [Pi.mul_def, neg_mul] using this
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  simp only [neg_mul, integral_neg] at h
  linarith

/-- PROVED. P0014 page 38, the display after 4.28, CORRECTED: integration by parts of - f'
against the error g_χ, here `bookError`. The boundary term f(y) g_χ(y) is KEPT; the printed
display drops it. The derivative of `bookError q t` is 0.15 / t. -/
theorem ibp_error (q : ℕ) [NeZero q] (δ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Set.Ioi T, tailEnvDeriv δ t * ZeroCount1623.bookError q t =
      tailEnv δ T * ZeroCount1623.bookError q T +
        ∫ t in Set.Ioi T, tailEnv δ t * (0.15 / t) := by
  have hT0 : 0 < T := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hu : ∀ x ∈ Set.Ioi T, HasDerivAt (fun t => -tailEnv δ t) (tailEnvDeriv δ x) x :=
    fun x _ => hasDerivAt_neg_tailEnv δ x
  have hv : ∀ x ∈ Set.Ioi T, HasDerivAt (fun t => ZeroCount1623.bookError q t) (0.15 / x) x :=
    fun x hx => hasDerivAt_bookError q (hT0.trans hx)
  have hb15 : ∀ t, T ≤ t → |0.15 / t| ≤ 1 * t ^ 2 := by
    intro t ht
    have : (1:ℝ) ≤ t := hT.trans ht
    rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]; nlinarith
  have hc15 : ContinuousOn (fun t : ℝ => 0.15 / t) (Set.Ici T) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; have : (1:ℝ) ≤ t := hT.trans ht; simp only [id]; positivity
  have huv' : IntegrableOn ((fun t => -tailEnv δ t) * fun t => 0.15 / t) (Set.Ioi T) := by
    have := ((integrable_env_mul δ hT _ hc15 hb15).1).neg
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp
  have hu'v : IntegrableOn (tailEnvDeriv δ * fun t => ZeroCount1623.bookError q t)
      (Set.Ioi T) := (ibp_integrable q δ hT).2
  have hcont : ContinuousAt (fun t => -tailEnv δ t * ZeroCount1623.bookError q t) T := by
    apply ContinuousAt.mul (continuous_tailEnv δ).neg.continuousAt
    unfold ZeroCount1623.bookError
    exact ((continuousAt_const.mul (ContinuousAt.log (by fun_prop)
      (by positivity))).add continuousAt_const)
  have h_zero : Tendsto ((fun t => -tailEnv δ t) * fun t => ZeroCount1623.bookError q t)
      (𝓝[>] T) (𝓝 (-tailEnv δ T * ZeroCount1623.bookError q T)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto ((fun t => -tailEnv δ t) * fun t => ZeroCount1623.bookError q t)
      atTop (𝓝 0) := by
    have := (tendsto_tailEnv_mul δ _ (fun t ht => bookError_bound q (hT.trans ht))).neg
    simpa [Pi.mul_def, neg_mul] using this
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  simp only [neg_mul, integral_neg] at h
  linarith


/-! ## Repaired step -/

/-- PROVED from the LEAVES above, CONDITIONAL ON hB, the cited count of display 4.26, page 38,
and on hcor, Corollary 3.2 at k equal to 0, page 10. P0014 Lemma 4.5, page 41, displays 4.33 to
4.35, REPAIRED: the tail Mellin mass is summable and at most twice the right side of the sealed
`MainTail123.tail_mass_bound_leaf` plus the boundary term the paper drops after display 4.28.
No pairing, so χ may be complex. This is NOT the sealed statement, which stays open. -/
theorem tail_mass_bound_repaired (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : TailIdx χ T => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val) ≤
      2 * 4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * 4.226 * tailEnv δ T * ZeroCount1623.bookError q T := by
  have hT1 : (1 : ℝ) ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set U : ℝ → ℝ := fun t => 2 * (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T) +
    2 * (ZeroCount1623.bookError q t + ZeroCount1623.bookError q T) with hUdef
  obtain ⟨hgint, hGT⟩ := tailEnv_eq_integral δ hT0
  obtain ⟨hI1, hI2⟩ := ibp_integrable q δ hT1
  have hgU_eq : (fun t => tailEnvDeriv δ t * U t) =
      fun t => (2 * (tailEnvDeriv δ t * (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T)) +
        2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t)) + (2 * ZeroCount1623.bookError q T) * tailEnvDeriv δ t := by
    funext t; simp only [hUdef]; ring
  have hgU : IntegrableOn (fun t => tailEnvDeriv δ t * U t) (Set.Ioi T) := by
    rw [hgU_eq]
    exact ((hI1.const_mul 2).add (hI2.const_mul 2)).add (hgint.const_mul (2 * ZeroCount1623.bookError q T))
  have hU : ∀ t, T < t → twoSidedCount χ t - twoSidedCount χ T ≤ U t :=
    fun t ht => count_increment_le hB χ hχ hT1 ht.le
  obtain ⟨hsum, hle⟩ := layer_cake_le χ T (tailEnvDeriv δ) U
    (fun t ht => tailEnvDeriv_nonneg δ (hT0.trans ht.le)) hgint hU hgU
  have hpt : ∀ ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val ≤
      4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t) := by
    intro ρ
    rw [← (tailEnv_eq_integral δ (abs_nonneg ρ.val.im)).2]
    exact mass_le_tailEnv χ δ T hT hcor ρ
  have hsumM : Summable (fun ρ : TailIdx χ T => mellinMassTerm χ δ ρ.val) :=
    MainTail123.tail_mass_summable_of_book hB q χ hχ δ T hT hcor
  refine ⟨hsumM, ?_⟩
  -- the integral of g U
  have hint : ∫ t in Set.Ioi T, tailEnvDeriv δ t * U t =
      2 * (∫ t in Set.Ioi T, tailEnv δ t * mainDensity q t) +
        2 * (∫ t in Set.Ioi T, tailEnv δ t * (0.15 / t)) +
          4 * (tailEnv δ T * ZeroCount1623.bookError q T) := by
    have hA : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T))) (Set.Ioi T) :=
      hI1.const_mul 2
    have hB2 : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t))
        (Set.Ioi T) := hI2.const_mul 2
    have hC : IntegrableOn (fun t => 2 * ZeroCount1623.bookError q T * tailEnvDeriv δ t)
        (Set.Ioi T) := hgint.const_mul _
    have hAB : IntegrableOn (fun t => 2 * (tailEnvDeriv δ t *
        (ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T)) +
          2 * (tailEnvDeriv δ t * ZeroCount1623.bookError q t)) (Set.Ioi T) := hA.add hB2
    rw [hgU_eq, integral_add hAB hC, integral_add hA hB2,
      integral_const_mul, integral_const_mul, integral_const_mul, ← hGT,
      ibp_main q δ hT1, ibp_error q δ hT1]
    ring
  have hdens := density_integral_le q δ hT1
  rw [tailEnv_integral_split q δ hT1] at hdens
  calc (∑' ρ : TailIdx χ T, mellinMassTerm χ δ ρ.val)
      ≤ ∑' ρ : TailIdx χ T,
          4.226 * ((ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t) :=
        hsumM.tsum_le_tsum hpt (hsum.mul_left 4.226)
    _ = 4.226 * ∑' ρ : TailIdx χ T,
          (ZeroCount1623.mult χ ρ.val : ℝ) * ∫ t in Set.Ioi |ρ.val.im|, tailEnvDeriv δ t := tsum_mul_left
    _ ≤ 4.226 * ∫ t in Set.Ioi T, tailEnvDeriv δ t * U t := by gcongr
    _ = _ := by rw [hint]
    _ ≤ _ := by linarith [hdens]

end LeanLab.HelfgottMajor.Prep1121TailRepair

#print axioms LeanLab.HelfgottMajor.Prep1121TailRepair.tail_mass_bound_repaired
#print axioms LeanLab.HelfgottMajor.Prep1121TailRepair.count_increment_le
#print axioms LeanLab.HelfgottMajor.Prep1121TailRepair.mass_le_tailEnv
