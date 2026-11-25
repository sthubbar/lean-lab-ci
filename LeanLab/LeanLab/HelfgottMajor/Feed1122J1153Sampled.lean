import LeanLab.HelfgottMajor.Feed1122DecompJ1153
import LeanLab.HelfgottMajor.Decomp526a

/-!
Split of `Feed1122DecompJ1153.leaf_middle_sampled_mass_le`, burst-20261122 session S125.

The target bounds the sum over zeros with `1 < |im ρ| ≤ T` of multiplicity times the squared
Gaussian Mellin norm by `(nTwo + nLog) log (q T)`. The book route of P0014 pages 38 to 40 is
followed for the squared profile: the zeros sit on the critical line, the sum splits by the sign
of the ordinate, each sign is a Stieltjes sum against the half endpoint zero count, and finite
atom partial summation from `Decomp526a` turns it into the integral of the count main term
against the squared profile, plus the count error of book display 16.21 times the boundary
values and the total variation of the squared profile.

Reused inputs, no new copies:
* `ZeroCount1623.book_zero_count`, the open LEAF for the count of display 4.26 in book form,
  through `Decomp526a.signed_count_bound`;
* `Decomp526a.finite_atom_count_error_bound`, proved partial summation against a count envelope;
* `Decomp389b.line_integral_sum`, the proved Mellin Plancherel identity of display 4.42.

The main term is then at most `nTwo log (q T)` with no new input. The count error carries an
additive constant `3.389` per unit of variation, so it is absorbed by `nLog log (q T)` only for
`q T` large. Two LEAF pieces remain:
* `leaf_gaussian_sq_profile_variation_le`, a pure Gaussian Mellin estimate with no character,
  zero or conductor: boundary values plus total variation of the squared profile on both
  signs of the line, from height 1 to height T, is at most 8;
* `leaf_middle_sampled_mass_small_range`, the range `q T < exp 41` where the additive count
  constant cannot be absorbed by partial summation.

The twin `leaf_middle_sampled_mass_le_s125` has exactly the statement of the target.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122J1153Sampled
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a Decomp269b DecompJ1153
open Decomp389b Decomp526a ZeroCount1623

/-- LEAF: P0014 page 40, the count error step after display 4.31, book Part IV page 434
after display 16.26. Class MEDIUM: a pure estimate for the Gaussian Mellin transform of
display 4.42 on page 43, with no character, zero or conductor.
For either sign of the line, the squared profile `t ↦ ‖F_δ(1/2 + i ε t)‖²` has value at height
1, value at height `T` and total variation on `[1, T]` adding up, over both signs, to at most 8.
S125 numerics on a grid of `δ` give at most about 6.36; see the notes file. Not a proof. -/
theorem leaf_gaussian_sq_profile_variation_le (δ T : ℝ) (hT : 1 ≤ T) :
    (‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ^ 2 +
        ∫ t in (1 : ℝ)..T,
          |deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) t|) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ∫ t in (1 : ℝ)..T,
          |deriv (fun u : ℝ =>
            ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-u : ℝ) : ℂ) * Complex.I)‖ ^ 2) t|) ≤ 8 := by
  sorry

/-- LEAF: P0014 pages 38 to 40, displays 4.26 and 4.31 with the numerical verification of
zeros that P0014 takes from Platt for small conductor and height, compare display 4.42 on
page 43. Class HARD. The range `q T < exp 41`, where the additive constant 3.389 of the count
error in book display 16.21 is too large for partial summation, so the sampled mass must be
bounded from the actual low zeros. This is the target restricted to that bounded range. -/
theorem leaf_middle_sampled_mass_small_range (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T) (hsmall : (q : ℝ) * T < exp 41)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤
      (Sec45.nTwo + Sec45.nLog) * log (q * T) := by
  sorry

/-- PROVED. Squared Gaussian profile on either sign of the line is absolutely continuous,
from the proved norm profile of `Decomp526a`. Support for display 4.31 on page 39. -/
theorem gaussian_sq_absolutelyContinuous (δ ε a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2) a b := by
  have h := gaussian_norm_absolutelyContinuous δ ε a b
  have hm := h.mul h
  convert hm using 1
  funext t
  simp only [Pi.mul_apply, sq]
  rfl

/-- PROVED. Lower bound for the log weighted norm of display 4.42, page 43, from
`γ > 1/2`, `log 2 > 0.693` and `π > 3.14159`. -/
theorem nLog_ge : (1.87 : ℝ) ≤ Sec45.nLog := by
  unfold Sec45.nLog
  have hs := Sec45.sqrt_pi_gt
  have hp := pi_gt_d6
  have hγ := one_half_lt_eulerMascheroniConstant
  have hl := log_two_gt_d9
  have hin : (16.98 : ℝ) ≤ π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
      8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 := by
    nlinarith
  have hpos : (0 : ℝ) ≤ √π / 16 := by positivity
  calc (1.87 : ℝ) ≤ 1.7724538 / 16 * 16.98 := by norm_num
    _ ≤ √π / 16 * 16.98 := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hin hpos

/-- PROVED, CONDITIONAL ON the signed count bound, that is `ZeroCount1623.book_zero_count`.
One sign of the squared sampled mass: finite atom partial summation of display 4.31 against
the count of display 4.26, book page 431, with the main term bounded by the line energy
and the count error by the boundary values and total variation of the squared profile. -/
theorem one_sign_sq_sampling (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1)
    (hcount : ∀ t : ℝ, 1 ≤ t →
      |ZeroCount1623.bookCount (if ε = 1 then χ else χ⁻¹) t -
        ZeroCount1623.bookMain q t| ≤ ZeroCount1623.bookError q t) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        if 1 < ε * ρ.im then
          (if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * (ε * ρ.im) : ℝ) * Complex.I)‖ ^ 2 else 0) ≤
      max (log ((q : ℝ) * T / (2 * π))) 0 * lineEnergy δ ε / (2 * π) +
        bookError q T *
          (‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * 1 : ℝ) * Complex.I)‖ ^ 2 +
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * T : ℝ) * Complex.I)‖ ^ 2 +
            ∫ t in (1 : ℝ)..T,
              |deriv (fun u : ℝ =>
                ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * u : ℝ) * Complex.I)‖ ^ 2) t|) := by
  classical
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  let s := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im)
  let γ : ℂ → ℝ := fun ρ => ε * ρ.im
  let w : ℂ → ℝ := fun ρ => if ε * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)
  let f : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2
  have hAll : ∀ ρ ∈ s, γ ρ ≤ T := by
    intro ρ hρ
    have hρs : ρ ∈ stripZeros χ T := by simpa [s] using (Finset.mem_filter.mp hρ).1
    calc
      γ ρ ≤ |ε * ρ.im| := le_abs_self _
      _ = |ρ.im| := by rw [abs_mul, habs, one_mul]
      _ ≤ _ := hρs.2.2.2
  have hclosed (t : ℝ) (ht : t ∈ Icc 1 T) :
      |(∑ ρ ∈ s, if γ ρ ≤ t then w ρ else 0) - bookMain q t| ≤ bookError q t := by
    change |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
      if ε * ρ.im ≤ t then w ρ else 0) - bookMain q t| ≤ bookError q t
    rw [signed_strip_cutoff_sum χ w T t ε ht.2 hε]
    exact signed_finite_count_bound χ t ε ht.1 hε hcount
  have hupper : |(∑ ρ ∈ s, w ρ) - bookMain q T| ≤ bookError q T :=
    signed_finite_count_bound χ T ε hT hε hcount
  have hlower := hclosed 1 ⟨le_rfl, hT⟩
  have hAE : ∀ᵐ t ∂volume.restrict (Icc 1 T),
      |(∑ ρ ∈ s, if γ ρ < t then w ρ else 0) - bookMain q t| ≤ bookError q t := by
    filter_upwards [ae_restrict_of_ae (finite_cumulative_lt_eq_le_ae s γ w),
      ae_restrict_mem measurableSet_Icc] with t he ht
    rw [he]
    exact hclosed t ht
  have hfac : AbsolutelyContinuousOnInterval f 1 T := gaussian_sq_absolutelyContinuous δ ε 1 T
  have hg : ContinuousOn (bookError q) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    unfold bookError
    fun_prop (disch := positivity)
  have hAbel := finite_atom_count_error_bound s γ w f (bookMain q) (bookError q) 1 T hT
    hAll hfac (bookMain_absolutelyContinuous q T hT) hg hAE hupper hlower
  -- the left side of hAbel is the left side of the goal
  change (∑ ρ ∈ s, if 1 < γ ρ then w ρ * f (γ ρ) else 0) ≤ _
  refine hAbel.trans ?_
  -- main term
  have hfc : ContinuousOn f (uIcc 1 T) :=
    ((signed_profile_continuous δ ε).norm.pow 2).continuousOn
  have hlogc : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t / (2 * π))) (uIcc 1 T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hmainEq : (∫ t in (1 : ℝ)..T, f t * deriv (bookMain q) t) =
      (∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π))) / (2 * π) := by
    calc
      _ = ∫ t in (1 : ℝ)..T, (1 / (2 * π)) * (f t * log ((q : ℝ) * t / (2 * π))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        dsimp only
        rw [(bookMain_hasDerivAt q t (lt_of_lt_of_le zero_lt_one ht.1)).deriv]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; ring
  set A := max (log ((q : ℝ) * T / (2 * π))) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  have hptw : ∀ t ∈ Icc (1 : ℝ) T, f t * log ((q : ℝ) * t / (2 * π)) ≤ A * f t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hf0 : 0 ≤ f t := sq_nonneg _
    have hlog : log ((q : ℝ) * t / (2 * π)) ≤ A := by
      refine le_trans ?_ (le_max_left _ _)
      apply log_le_log (by positivity)
      have : (q : ℝ) * t ≤ q * T := mul_le_mul_of_nonneg_left ht.2 hq0.le
      exact div_le_div_of_nonneg_right this (by positivity)
    nlinarith
  have hint1 : (∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π))) ≤
      ∫ t in (1 : ℝ)..T, A * f t :=
    intervalIntegral.integral_mono_on hT (hfc.mul hlogc).intervalIntegrable
      (continuousOn_const.mul hfc).intervalIntegrable hptw
  have hFE : (∫ t in (1 : ℝ)..T, f t) ≤ lineEnergy δ ε := by
    rw [intervalIntegral.integral_of_le hT]
    apply setIntegral_mono_set (signed_profile_sq_integrable δ ε hε).integrableOn
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    filter_upwards with t ht
    exact lt_trans zero_lt_one ht.1
  have hmain : (∫ t in (1 : ℝ)..T, f t * deriv (bookMain q) t) ≤ A * lineEnergy δ ε / (2 * π) := by
    rw [hmainEq]
    apply div_le_div_of_nonneg_right _ (show 0 ≤ 2 * π by positivity)
    calc _ ≤ ∫ t in (1 : ℝ)..T, A * f t := hint1
      _ = A * ∫ t in (1 : ℝ)..T, f t := intervalIntegral.integral_const_mul _ _
      _ ≤ A * lineEnergy δ ε := mul_le_mul_of_nonneg_left hFE hA0
  -- error terms
  have hgmono : ∀ t ∈ Icc (1 : ℝ) T, bookError q t ≤ bookError q T := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    unfold bookError
    have : log ((q : ℝ) * t) ≤ log ((q : ℝ) * T) :=
      log_le_log (by positivity) (mul_le_mul_of_nonneg_left ht.2 hq0.le)
    linarith
  have hgT0 : 0 ≤ bookError q T := by
    unfold bookError
    have : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
    linarith
  have hdi : IntervalIntegrable (fun t => |deriv f t| * bookError q t) volume 1 T := by
    simpa only [Real.norm_eq_abs] using hfac.intervalIntegrable_deriv.norm.mul_continuousOn hg
  have hdi2 : IntervalIntegrable (fun t => |deriv f t| * bookError q T) volume 1 T := by
    simpa only [Real.norm_eq_abs] using hfac.intervalIntegrable_deriv.norm.mul_const _
  have herr : (∫ t in (1 : ℝ)..T, |deriv f t| * bookError q t) ≤
      bookError q T * ∫ t in (1 : ℝ)..T, |deriv f t| := by
    calc _ ≤ ∫ t in (1 : ℝ)..T, |deriv f t| * bookError q T := by
          apply intervalIntegral.integral_mono_on hT hdi hdi2
          intro t ht
          exact mul_le_mul_of_nonneg_left (hgmono t ht) (abs_nonneg _)
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  have hg1 := hgmono 1 ⟨le_rfl, hT⟩
  have hfT : |f T| = f T := abs_of_nonneg (sq_nonneg _)
  have hf1 : |f 1| = f 1 := abs_of_nonneg (sq_nonneg _)
  have hf10 : 0 ≤ f 1 := sq_nonneg _
  rw [hfT, hf1]
  have hb : f 1 * bookError q 1 ≤ f 1 * bookError q T := mul_le_mul_of_nonneg_left hg1 hf10
  change _ ≤ A * lineEnergy δ ε / (2 * π) +
    bookError q T * (f 1 + f T + ∫ t in (1 : ℝ)..T, |deriv f t|)
  linarith

/-- PROVED. The middle sampled sum is the sum of the two signed atom sums, using the critical
line hypothesis to replace each zero by `1/2 + i im ρ`. P0014 display 4.32 on page 39. -/
theorem sampled_mass_signed_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ =
      (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ (1 : ℝ) * ρ.im),
        if 1 < (1 : ℝ) * ρ.im then
          (if (1 : ℝ) * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) * ((1 : ℝ) * ρ.im) : ℝ) * Complex.I)‖ ^ 2
          else 0) +
      (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ (-1 : ℝ) * ρ.im),
        if 1 < (-1 : ℝ) * ρ.im then
          (if (-1 : ℝ) * ρ.im = 0 then (mult χ ρ : ℝ) / 2 else (mult χ ρ : ℝ)) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) * ((-1 : ℝ) * ρ.im) : ℝ) * Complex.I)‖ ^ 2
          else 0) := by
  classical
  let F : ℂ → ℝ := fun z => if |z.im| ≤ 1 then 0 else
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) * ‖gaussianMellin δ z‖ ^ 2
  have h1 : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) = ∑' ρ : ZeroIdx χ T, F ρ.val := by
    apply tsum_congr
    intro ρ
    by_cases h : |ρ.val.im| ≤ 1
    · simp [F, Set.indicator, h]
    · simp [F, Set.indicator, h]
  rw [h1, tsum_zeroIdx χ T F, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρs : ρ ∈ stripZeros χ T := by simpa using hρ
  have hz := hzeros ρ hρs.1 hρs.2.1 hρs.2.2.1 hρs.2.2.2
  have he : ρ = (1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hG : ‖gaussianMellin δ ρ‖ = ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I)‖ :=
    congrArg (fun z => ‖gaussianMellin δ z‖) he
  have hnn : (-1 : ℝ) * ((-1 : ℝ) * ρ.im) = ρ.im := by ring
  simp only [F, one_mul, hnn, mult]
  by_cases hp : 1 < ρ.im
  · have hn : ¬1 < -1 * ρ.im := by linarith
    have hn' : ¬1 < -ρ.im := by linarith
    have ha : ¬|ρ.im| ≤ 1 := by intro h; have := (abs_le.mp h).2; linarith
    have hp0 : 0 ≤ ρ.im := by linarith
    have hne : ρ.im ≠ 0 := by linarith
    simp [ha, hp, hn, hn', hp0, hne, hG]
  · by_cases hn : 1 < -1 * ρ.im
    · have ha : ¬|ρ.im| ≤ 1 := by intro h; have := (abs_le.mp h).1; linarith
      have hn0 : 0 ≤ -1 * ρ.im := by linarith
      have hne : -1 * ρ.im ≠ 0 := by linarith
      have hn' : 1 < -ρ.im := by linarith
      have hn0' : 0 ≤ -ρ.im := by linarith
      have hne' : -ρ.im ≠ 0 := by linarith
      have hne'' : ρ.im ≠ 0 := by linarith
      simp [ha, hp, hn, hn0, hne, hn', hn0', hne', hne'', hG]
    · have ha : |ρ.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hn' : ¬1 < -ρ.im := by linarith
      simp [ha, hp, hn, hn']

/-- PROVED, CONDITIONAL ON `ZeroCount1623.book_zero_count` through the signed count bound and
on `leaf_gaussian_sq_profile_variation_le`. The large range `exp 41 ≤ q T` of the sampling
inequality: the main term is at most `nTwo log (q T)` by the Plancherel identity of display
4.42, and the count error `(0.15 log (q T) + 3.389) · 8` is absorbed by `nLog log (q T)`. -/
theorem middle_sampled_mass_large (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T) (hlarge : exp 41 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤
      (Sec45.nTwo + Sec45.nLog) * log (q * T) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  rw [sampled_mass_signed_split q χ δ T hzeros]
  have hP := one_sign_sq_sampling q χ δ T 1 hT (Or.inl rfl)
    (signed_count_bound χ hχ 1 · ·)
  have hN := one_sign_sq_sampling q χ δ T (-1) hT (Or.inr rfl)
    (signed_count_bound χ hχ (-1) · ·)
  have hV := leaf_gaussian_sq_profile_variation_le δ T hT
  have hV' : (‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) * 1 : ℝ) * Complex.I)‖ ^ 2 +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) * T : ℝ) * Complex.I)‖ ^ 2 +
        ∫ t in (1 : ℝ)..T, |deriv (fun u : ℝ =>
          ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) * u : ℝ) * Complex.I)‖ ^ 2) t|) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) * 1 : ℝ) * Complex.I)‖ ^ 2 +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) * T : ℝ) * Complex.I)‖ ^ 2 +
        ∫ t in (1 : ℝ)..T, |deriv (fun u : ℝ =>
          ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) * u : ℝ) * Complex.I)‖ ^ 2) t|) ≤ 8 := by
    simpa only [one_mul, neg_one_mul, mul_one, Complex.ofReal_neg, Complex.ofReal_one] using hV
  -- Plancherel
  have hpl := line_integral_sum δ
  have hE1 : lineEnergy δ 1 = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  have hE2 : lineEnergy δ (-1) = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  have hsum : lineEnergy δ 1 + lineEnergy δ (-1) = 2 * π * Sec45.nTwo := by
    rw [hE1, hE2]; exact hpl
  -- the log factor
  have hL41 : (41 : ℝ) ≤ log ((q : ℝ) * T) := (le_log_iff_exp_le hqT).mpr hlarge
  have h2pi : (1 : ℝ) ≤ 2 * π := by linarith [pi_gt_three]
  have hA : max (log ((q : ℝ) * T / (2 * π))) 0 ≤ log ((q : ℝ) * T) := by
    apply max_le
    · apply log_le_log (by positivity)
      exact div_le_self hqT.le h2pi
    · linarith
  have hE1n : 0 ≤ lineEnergy δ 1 := by
    unfold lineEnergy
    apply setIntegral_nonneg measurableSet_Ioi; intro t _; positivity
  have hE2n : 0 ≤ lineEnergy δ (-1) := by
    unfold lineEnergy
    apply setIntegral_nonneg measurableSet_Ioi; intro t _; positivity
  have hpi : 0 < 2 * π := by positivity
  have hmain : max (log ((q : ℝ) * T / (2 * π))) 0 * lineEnergy δ 1 / (2 * π) +
      max (log ((q : ℝ) * T / (2 * π))) 0 * lineEnergy δ (-1) / (2 * π) ≤
      Sec45.nTwo * log ((q : ℝ) * T) := by
    have hA0 : 0 ≤ max (log ((q : ℝ) * T / (2 * π))) 0 := le_max_right _ _
    have heq : max (log ((q : ℝ) * T / (2 * π))) 0 * lineEnergy δ 1 / (2 * π) +
        max (log ((q : ℝ) * T / (2 * π))) 0 * lineEnergy δ (-1) / (2 * π) =
        max (log ((q : ℝ) * T / (2 * π))) 0 * Sec45.nTwo := by
      rw [← add_div, ← mul_add, hsum]; field_simp
    rw [heq]
    have := mul_le_mul_of_nonneg_right hA Decomp389b.nTwo_pos.le
    linarith
  have hnL := nLog_ge
  have hg : bookError q T = 0.15 * log ((q : ℝ) * T) + 3.389 := rfl
  have hg0 : 0 ≤ bookError q T := by rw [hg]; linarith
  have hgv := mul_le_mul_of_nonneg_left hV' hg0
  have hL0 : (0 : ℝ) ≤ log ((q : ℝ) * T) := by linarith
  have hnLL := mul_le_mul_of_nonneg_right hnL hL0
  rw [hg] at hP hN hgv
  linarith

/-- Exactly `Feed1122DecompJ1153.leaf_middle_sampled_mass_le`, assembled from the large range,
which is proved conditional on `ZeroCount1623.book_zero_count` and
`leaf_gaussian_sq_profile_variation_le`, and the small range LEAF
`leaf_middle_sampled_mass_small_range`. It has no open proof obligation of its own. -/
theorem leaf_middle_sampled_mass_le_s125 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤
      (Sec45.nTwo + Sec45.nLog) * log (q * T) := by
  by_cases h : exp 41 ≤ (q : ℝ) * T
  · exact middle_sampled_mass_large q χ hχ δ T hT h hzeros
  · exact leaf_middle_sampled_mass_small_range q χ hχ δ T hT (lt_of_not_ge h) hzeros

end LeanLab.HelfgottMajor.Feed1122J1153Sampled
