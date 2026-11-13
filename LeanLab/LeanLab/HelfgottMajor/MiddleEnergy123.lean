import Mathlib
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottMajor.Gamma431
import LeanLab.HelfgottMajor.Sec45
import LeanLab.HelfgottMajor.HalfMoment389
import LeanLab.HelfgottMajor.BookP1617
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Route burst session 8, 2026-11-12, step gaussian_explicit_estimate p3.
An upstream copy of the lab supply for P0014 Lemma 4.4, pages 38 to 40, in the book form of
Part IV pages 433 and 434, Lemma 16.10 and display 16.26: the middle mass bound of
SplitGaussian123, proved from the sampling leaf, the two Mellin Plancherel energies and the
small height branch. The energies and the small branch are PROVED in the lab files
LogMoment431, Decomp389c and Decomp389b, which import Decomp123 and so cannot be imported by
SplitGaussian123. Their text is copied here verbatim inside sub namespaces of the same names,
with the definitions gaussianMellin, mellinMassTerm and middleMass copied from Decomp269a and
Decomp269b, which have the same bodies as those of SplitGaussian123. The one LEAF,
Decomp389b.middle_sampling_bound, is copied with its statement unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MiddleEnergy123.Decomp269a
open Real LeanLab.HelfgottArcs

/-- Copy of Decomp269a.gaussianMellin, the same body as SplitGaussian123.gaussianMellin. -/
noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end LeanLab.HelfgottMajor.MiddleEnergy123.Decomp269a

namespace LeanLab.HelfgottMajor.MiddleEnergy123.Decomp269b
open Real LeanLab.HelfgottArcs Decomp269a

/-- Copy of Decomp269b.mellinMassTerm. -/
noncomputable def mellinMassTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖gaussianMellin δ ρ‖

/-- Copy of Decomp269b.middleMass. -/
noncomputable def middleMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ ρ.val) ρ

end LeanLab.HelfgottMajor.MiddleEnergy123.Decomp269b

namespace LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389a
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a

/-- PROVED. Copy of Gaussian269.mellin_norm_le, display 4.30 on page 39. -/
theorem mellin_norm_le (δ : ℝ) (s : ℂ) :
    ‖gaussianMellin δ s‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), t ^ (s.re - 1) * exp (-t ^ 2 / 2) := by
  unfold gaussianMellin mellin
  calc
    _ ≤ ∫ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
      rw [norm_smul, norm_mul, he, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      simp

/-- PROVED. Copy of Decomp389a.mellin_critical_norm_le, CONDITIONAL ON hhalf. -/
theorem mellin_critical_norm_le (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2)
    (hhalf : (∫ t in Set.Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2)) ≤
      2.15581) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 := by
  have h := mellin_norm_le δ s
  rw [hs] at h
  exact h.trans hhalf

end LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389a

namespace LeanLab.HelfgottMajor.MiddleEnergy123.LogMoment431
open MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The second Gamma derivative is its log squared integral at one half.
Source P0014 page 43 display 4.42, symbolic scalar integration.
-/
theorem gamma_second_log_integral :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
      ((Real.log t ^ 2 * Real.exp (-t) : ℝ) : ℂ)) =
      deriv (deriv Complex.Gamma) (1 / 2 : ℂ) := by
  let f : ℝ → ℂ := fun t => ((Real.log t * Real.exp (-t) : ℝ) : ℂ)
  have hc : ContinuousOn f (Ioi (0 : ℝ)) := by
    intro t ht
    unfold f
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt ht)).mul
        (Real.continuous_exp.comp continuous_neg).continuousAt)).continuousWithinAt
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(1 : ℝ))) := by
    have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).isBigO
    have he : (fun t : ℝ => Real.exp (-t)) =O[atTop] (fun t : ℝ => t ^ (-2 : ℝ)) := by
      simpa only [one_mul, neg_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-2)).isBigO
    have hh := hl.mul he
    have hh' : (fun t : ℝ => Real.log t * Real.exp (-t)) =O[atTop]
        (fun t : ℝ => t ^ (-(1 : ℝ))) := by
      apply hh.congr' (Filter.Eventually.of_forall fun _ => rfl)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      norm_num
    rw [← isBigO_norm_left]
    simpa only [f, Complex.norm_real, isBigO_norm_left] using hh'
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(1 / 4 : ℝ))) := by
    have hl := (isLittleO_log_rpow_nhdsGT_zero (by norm_num : (-(1 / 4 : ℝ)) < 0)).isBigO
    have hexp : ContinuousWithinAt (fun t : ℝ => Real.exp (-t)) (Ioi 0) 0 :=
      (Real.continuous_exp.comp continuous_neg).continuousWithinAt
    have he : (fun t : ℝ => Real.exp (-t)) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto (by simpa using! hexp) one_ne_zero
    have hh := hl.mul he
    rw [← isBigO_norm_left]
    simpa only [f, Complex.norm_real, isBigO_norm_left, mul_one] using hh
  have hd := (mellin_hasDerivAt_of_isBigO_rpow
    (hc.locallyIntegrableOn measurableSet_Ioi) htop (by norm_num : (1 / 2 : ℂ).re < 1)
    hbot (by norm_num : (1 / 4 : ℝ) < (1 / 2 : ℂ).re)).2
  have hfirst (s : ℂ) (hs : 0 < s.re) : deriv Complex.Gamma s = mellin f s := by
    simpa only [mellin, f, smul_eq_mul, Complex.ofReal_mul] using
      (Complex.hasDerivAt_Gamma_of_re_pos hs).deriv
  have heq : deriv Complex.Gamma =ᶠ[𝓝 (1 / 2 : ℂ)] mellin f := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 / 2 : ℂ).re by norm_num)] with z hz
    exact hfirst z hz
  have hres := (hd.congr_of_eventuallyEq heq).deriv
  rw [hres]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [f, smul_eq_mul, RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [show (1 / 2 : ℂ) - 1 = ((-(1 / 2 : ℝ)) : ℂ) by norm_num]
  change (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) * ((Real.log t : ℂ) ^ 2 * (Real.exp (-t) : ℂ)) =
    (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
      ((Real.log t : ℂ) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
  ring

/-- The scalar Gamma log squared integral has the explicit special function value.
Source P0014 page 43 display 4.42 before the square substitution.
-/
theorem scalar_gamma_log_square_integral :
    (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t ^ 2 * Real.exp (-t))) =
      Real.sqrt Real.pi * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) := by
  apply Complex.ofRealLI.injective
  have hh := gamma_second_log_integral
  rw [Gamma431.deriv2_Gamma_one_half] at hh
  calc
    _ = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) *
        ((Real.log t ^ 2 * Real.exp (-t) : ℝ) : ℂ) := by
      rw [← LinearIsometry.integral_comp_comm]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have hpow := Complex.ofReal_cpow ht.le (-(1 / 2 : ℝ))
      simp only [Complex.ofReal_neg] at hpow
      rw [← hpow]
      simp only [Complex.ofRealLI_apply, Complex.ofReal_mul]
    _ = _ := hh
    _ = _ := by
      simp only [Complex.ofRealLI_apply, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofNat_log]

/-- The square substitution multiplies the Gaussian log squared moment by eight.
Source P0014 page 43 display 4.42, symbolic integration.
-/
theorem gaussian_log_square_substitution :
    (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t ^ 2 * Real.exp (-t))) =
      8 * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) * Real.log t ^ 2 := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ)) (by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpow : (t ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
    rw [← Real.rpow_mul ht.le]
    norm_num
    exact Real.rpow_neg_one t
  dsimp only
  rw [hpow, Real.log_rpow ht]
  norm_num only [Real.rpow_two, Real.rpow_one, smul_eq_mul]
  field_simp
  <;> ring

/-- The exact scalar Gaussian log squared moment from P0014 page 43 display 4.42.
No Fourier, character or zero input is used.
-/
theorem gaussian_log_square_integral :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) * Real.log t ^ 2) = Sec45.nLog := by
  have h1 := scalar_gamma_log_square_integral
  rw [gaussian_log_square_substitution] at h1
  unfold Sec45.nLog
  linear_combination (1 / 8 : ℝ) * h1

end LeanLab.HelfgottMajor.MiddleEnergy123.LogMoment431

namespace LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The multiplicity counting summand N of T in display 4.26 on page 38. -/
noncomputable def stripCountTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)

/-- LEAF. Page 38, displays 4.25 and 4.26, the upper side of the classical count formula.
This counts all strip zeros up to T and estimates no Mellin value.
REPAIRED 2026-11-06: proved from `ZeroCount1623.strip_count`, CONDITIONAL ON
`ZeroCount1623.book_zero_count`, the shared book count of display 3.95. -/
theorem strip_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (stripCountTerm χ T) ∧
      (∑' ρ, stripCountTerm χ T ρ) ≤
        T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * T) + 17.7 :=
  ⟨ZeroCount1623.summable_zeroIdx χ T (stripCountTerm χ T),
    ZeroCount1623.strip_count χ hχ T hT⟩

/-- The critical line half moment bounds the middle mass by the total multiplicity count.
CONDITIONAL ON hzeros and the supplied count summability. Pages 39 and 40, display 4.30.
-/
theorem middle_mass_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcount : Summable (stripCountTerm χ T)) :
    middleMass χ δ T ≤ 2.15581 * ∑' ρ, stripCountTerm χ T ρ := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    -- copy edit: summability from the finiteness in ZeroCount1623, instead of Zeros269
    exact ZeroCount1623.summable_zeroIdx χ T _
  unfold middleMass
  rw [← tsum_mul_left]
  apply (hm.indicator _).tsum_le_tsum _ (hcount.mul_left 2.15581)
  intro ρ
  have hρ : 0 ≤ stripCountTerm χ T ρ := Nat.cast_nonneg _
  by_cases h : |ρ.val.im| ≤ 1
  · simp [Set.indicator, h]
    positivity
  · simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq, h, not_false_eq_true,
      ite_true, mellinMassTerm, stripCountTerm]
    have hz := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2
    have hb := Decomp389a.mellin_critical_norm_le δ ρ.val hz
      HalfMoment389.gaussian_half_moment_bound
    simpa only [stripCountTerm, mul_comm] using mul_le_mul_of_nonneg_left hb hρ

/-- A coarse lower bound for the positive square root T coefficient on page 40.
This is used only to cover the small qT range without the book lower height assumption.
-/
theorem middle_constant_ge :
    (15 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hNL : (1 : ℝ) ≤ Sec45.nLog := by
    unfold Sec45.nLog
    have hg : 0 ≤ eulerMascheroniConstant := by
      have := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
      linarith
    have hl : 0 ≤ log 2 := log_nonneg (by norm_num)
    have hl1 := log_two_gt_d9
    have hp := pi_gt_three
    have hs : (1.7 : ℝ) ≤ sqrt π := by linarith [Sec45.sqrt_pi_gt]
    have hb : (10 : ℝ) ≤ π ^ 2 + 2 * eulerMascheroniConstant ^ 2 +
        8 * eulerMascheroniConstant * log 2 + 8 * log 2 ^ 2 := by
      nlinarith [mul_nonneg hg hl, sq_nonneg eulerMascheroniConstant]
    calc
      (1 : ℝ) ≤ 1.7 / 16 * 10 := by norm_num
      _ ≤ _ := mul_le_mul (by linarith : (1.7 : ℝ) / 16 ≤ sqrt π / 16) hb
        (by norm_num) (by positivity)
  have hL : (1 : ℝ) ≤ sqrt Sec45.nLog :=
    (Real.le_sqrt (by norm_num) Sec45.nLog_nonneg).mpr (by simpa using hNL)
  have hN := Sec45.sqrt_nTwo_lt
  have hN0 := sqrt_nonneg Sec45.nTwo
  obtain ⟨hC0, hC⟩ := BookP1617.K_bds
  have hprod : log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo ≤ 2.3378771 * 0.941397 :=
    mul_le_mul hC.le hN.le hN0 (by norm_num)
  nlinarith

/-- Small qT is covered by the classical count formula and the scalar half moment.
This is the small height branch of the exact middle mass statement on page 40.
-/
theorem small_middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hsmall : (q : ℝ) * T ≤ 2 * π * exp 2)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have he2 : exp 2 < (8 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hcap : 2 * π * exp 2 ≤ (64 : ℝ) := by
    have hh := mul_le_mul pi_lt_four.le he2.le (exp_pos 2).le (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hT64 : T ≤ 64 := by nlinarith
  have hs0 := sqrt_nonneg T
  have hsq := sq_sqrt hT0.le
  have hs8 : sqrt T ≤ 8 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num; exact hT64⟩
  have hTs : T ≤ 8 * sqrt T := by nlinarith
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hlogmul : log ((q : ℝ) * T) = log (q : ℝ) + log T := log_mul hq0.ne' hT0.ne'
  have hlogT : log T ≤ T := by linarith [log_le_sub_one_of_pos hT0]
  have hratio : log ((q : ℝ) * T / (2 * π * exp 1)) ≤ 1 := by
    apply (log_le_iff_le_exp (by positivity)).mpr
    rw [div_le_iff₀ (by positivity)]
    have he : exp 1 * (2 * π * exp 1) = 2 * π * exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      ring
    rwa [he]
  obtain ⟨hcount, hbudget⟩ := strip_zero_count q χ hχ T hT
  have hm := middle_mass_le_count χ δ T hzeros hcount
  have hcount' : (∑' ρ, stripCountTerm χ T ρ) ≤ T / π +
      0.5 * (log (q : ℝ) + T) + 17.7 := by
    have hh := mul_le_mul_of_nonneg_left hratio (div_nonneg hT0.le pi_pos.le)
    rw [hlogmul] at hbudget
    linarith
  have hdiv : T / π ≤ T / 3 := by
    exact div_le_div_of_nonneg_left hT0.le (by norm_num) pi_gt_three.le
  have hmain : 0 ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) := by
    positivity
  have hc := mul_le_mul_of_nonneg_right middle_constant_ge hs0
  nlinarith

end LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389c

namespace LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389b
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b
open FourierTransform
open scoped SchwartzMap Topology ContDiff ENNReal

/-- The positive parameter half line energy on the critical line, book page 434.
The sign parameter is used only at 1 and minus 1 in the sampling proof.
-/
noncomputable def lineEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-- The derivative energy above height 1 on either sign of the line, book page 434. -/
noncomputable def derivativeEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ),
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-! ### Mellin Plancherel on the critical line, for the Gaussian integrand

The two energy leaves below are the sharp forms of
`∫ t, ‖mellin f (1/2 + t I)‖ ^ 2 = 2 * π * ∫ x in Ioi 0, ‖f x‖ ^ 2`
for `f x = exp (-x^2 / 2) * e (δ x)`, respectively for `log • f`. -/

lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e, Complex.norm_exp]
  have h : (2 * (π : ℂ) * Complex.I * (t : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Pointwise norm of the Gaussian-character integrand. -/
lemma gauss_norm (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ = exp (-x ^ 2 / 2) := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma gauss_norm_sq (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = exp (-x ^ 2) := by
  rw [gauss_norm, sq, ← Real.exp_add]
  congr 1
  ring

/-- Pointwise norm of the log-coordinate integrand `f (exp u) * exp (u / 2)`. -/
lemma log_norm (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = exp (u / 2) * exp (-(exp u) ^ 2 / 2) := by
  rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma log_norm_sq (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = exp u * exp (-(exp u) ^ 2) := by
  rw [log_norm, mul_pow]
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

lemma log_le_exp_abs (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤ exp (-|u| / 2) := by
  rw [log_norm]
  rcases le_total u 0 with hu | hu
  · have h1 : exp (-(exp u) ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by have := sq_nonneg (exp u); linarith)
    have h2 : exp (u / 2) = exp (-|u| / 2) := by rw [abs_of_nonpos hu]; ring_nf
    rw [h2]
    exact mul_le_of_le_one_right (exp_pos _).le h1
  · have h1 : exp (u / 2) * exp (-(exp u) ^ 2 / 2) = exp (u / 2 - (exp u) ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, abs_of_nonneg hu]
    refine Real.exp_le_exp.mpr ?_
    have he : 1 + 2 * u ≤ (exp u) ^ 2 := by
      have h := add_one_le_exp u
      have hp := exp_pos u
      nlinarith [sq_nonneg (exp u)]
    linarith

lemma integrable_exp_neg_abs_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => exp (-c * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => exp (-c * u)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using h
  have h2 : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iic 0) := by
    have h := h1.comp_neg
    rw [Set.neg_Ioi, neg_zero] at h
    have h' : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iio 0) := by
      refine h.congr_fun ?_ measurableSet_Iio
      intro u _
      show exp (-c * -u) = exp (c * u)
      rw [neg_mul_neg]
    exact (integrableOn_Iic_iff_integrableOn_Iio (f := fun u : ℝ => exp (c * u))).mpr h'
  have h3 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Ioi 0) := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro u hu
    show exp (-c * u) = exp (-c * |u|)
    rw [abs_of_pos (Set.mem_Ioi.mp hu)]
  have h4 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Iic 0) := by
    refine h2.congr_fun ?_ measurableSet_Iic
    intro u hu
    show exp (c * u) = exp (-c * |u|)
    rw [abs_of_nonpos (Set.mem_Iic.mp hu), neg_mul_neg]
  have hu : Set.Ioi (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
    exact lt_or_ge 0 x
  rw [← integrableOn_univ, ← hu]
  exact h3.union h4

lemma log_continuous (δ : ℝ) :
    Continuous (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  unfold e
  fun_prop

lemma log_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  refine Integrable.mono' (integrable_exp_neg_abs_mul (c := 1 / 2) (by norm_num))
    (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  rw [show -(1 / 2 : ℝ) * |u| = -|u| / 2 by ring]
  exact log_le_exp_abs δ u

lemma log_memLp (δ : ℝ) :
    MemLp (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) 2 := by
  have hg : MemLp (fun u : ℝ => exp (-|u| / 2)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm
      (by fun_prop : Continuous (fun u : ℝ => exp (-|u| / 2))).aestronglyMeasurable]
    refine (integrable_exp_neg_abs_mul (c := 1) (by norm_num)).congr ?_
    filter_upwards with u
    have hp : (0:ℝ) < exp (-|u| / 2) := exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hp, sq, ← Real.exp_add]
    congr 1
    rw [show -(1:ℝ) * |u| = -|u| by ring]
    ring
  refine MemLp.mono' hg (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact log_le_exp_abs δ u

/-- `exp u` is positive, so on the critical line the complex power times the
change-of-variables factor is a single exponential. -/
lemma cpow_exp_mul (u t : ℝ) :
    ((exp u : ℝ) : ℂ) * (((exp u : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) := by
  have hne : Complex.exp (u : ℂ) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero hne,
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), ← Complex.exp_add]
  congr 1
  ring

/-- The Mellin transform of the Gaussian-character integrand on the critical line is the
Fourier integral of its log coordinate transform. -/
theorem mellin_eq_fourier_gauss (δ : ℝ) (t : ℝ) :
    gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(t / (2 * π))) := by
  rw [show gaussianMellin δ = mellin (fun x : ℝ => (exp (-x ^ 2 / 2) : ℂ) * e (δ * x)) from rfl,
    mellin, fourier_eq']
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
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), Complex.ofReal_exp]
  simp only [inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    abs_of_pos (exp_pos u)]
  have hL : ((exp u : ℝ) : ℂ) *
      (Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1)) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hR : Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
      (((exp (u / 2) : ℝ) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp only [← Complex.ofReal_exp]
  exact hL.trans hR.symm


/-! ### Plancherel for the Fourier integral on `L1 ∩ L2`

Ported from the lab's `LeanLab.ExceptionalSet.WindowParseval264` (which uses Mathlib only). -/

theorem wip_fourier_pairing (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, g x * 𝓕 f x =
      ∫ x : ℝ, g x * (𝓕 (h₂.toLp f) : Lp ℂ 2) x := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
    (by fun_prop) g.integrable h₁
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    exact flip_innerₗ ℝ
  rw [hflip] at hswap
  have hd := congrArg (fun d : 𝓢'(ℝ, ℂ) => d g)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x : ℝ, (𝓕 g) x * f x := by
      simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul] using hswap.symm
    _ = ∫ x : ℝ, (𝓕 g) x * (h₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by simpa only [smul_eq_mul] using hd

theorem wip_fourierIntegral_ae_eq (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  simpa using wip_fourier_pairing f h₁ h₂ (hc'.toSchwartzMap hg')

theorem wip_integral_norm_sq_coe (u : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖u x‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    using hi.symm

theorem wip_integral_norm_sq_fourier (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ∫ t : ℝ, ‖𝓕 f t‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [wip_fourierIntegral_ae_eq f h₁ h₂] with t ht
      rw [ht]
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := wip_integral_norm_sq_coe _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      rw [← wip_integral_norm_sq_coe]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-! ### The `L2` mass in log coordinates -/

lemma log_sq_integral (δ : ℝ) :
    ∫ u : ℝ, ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = Sec45.nTwo := by
  have hIoi : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = Sec45.nTwo := by
    have h : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
        = ∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact gauss_norm_sq δ x
    rw [h, show (fun x : ℝ => exp (-x ^ 2)) = (fun x : ℝ => exp (-1 * x ^ 2)) from by
      funext x; ring_nf, integral_gaussian_Ioi]
    simp [Sec45.nTwo]
  have himg : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    rw [← Real.range_exp, ← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.exp_injective hxy)]
    simp only [abs_of_pos (exp_pos _), setIntegral_univ]
  have hpt : ∀ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
        = exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    intro u
    rw [log_norm_sq, gauss_norm_sq, smul_eq_mul]
  rw [show (∫ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2)
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with u
    exact hpt u]
  rw [← himg, hIoi]

lemma integrable_fourier_sq (δ : ℝ) :
    Integrable (fun ξ : ℝ =>
      ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) := by
  have h2 := log_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)] with ξ hξ
  rw [hξ]


lemma integrable_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) hR).mpr (integrable_fourier_sq δ)
  refine h.congr ?_
  filter_upwards with t
  rw [mellin_eq_fourier_gauss δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

lemma fourier_sq_integral (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2 = Sec45.nTwo := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)]
  exact log_sq_integral δ

theorem integral_mellin_sq_gauss (δ : ℝ) :
    ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nTwo := by
  have hpt : ∀ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
    intro t
    rw [mellin_eq_fourier_gauss δ t]
    have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
    rw [harg]
  rw [show ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ∫ t : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with t
    exact hpt t]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2)]
  rw [fourier_sq_integral δ]
  have hcoef : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_div, div_one, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef, smul_eq_mul]

/-- The two sign-split Mellin energies add up to `2 π` times the `L2` mass. -/
theorem line_integral_sum (δ : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      + (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = 2 * π * Sec45.nTwo := by
  set F : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 with hF
  have h1 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), F t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [one_mul]
    rw [hF]
  have himg : Neg.neg '' (Set.Ioi (0:ℝ)) = Set.Iio (0:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨-x, by linarith, by ring⟩
  have hsub : ∫ t in Set.Ioi (0 : ℝ), F (-t) = ∫ t in Set.Iio (0 : ℝ), F t := by
    rw [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      (fun x _ y _ hxy => neg_injective hxy)]
    simp
  have h2 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Iic (0 : ℝ), F t := by
    rw [show (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
        = ∫ t in Set.Ioi (0 : ℝ), F (-t) from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [neg_one_mul]
      rw [hF]]
    rw [hsub, integral_Iic_eq_integral_Iio]
  have hInt : Integrable F := integrable_mellin_sq δ
  rw [h1, h2]
  rw [← Set.compl_Ioi (a := (0:ℝ))]
  rw [integral_add_compl measurableSet_Ioi hInt]
  exact integral_mellin_sq_gauss δ

lemma nTwo_pos : 0 < Sec45.nTwo := by
  rw [Sec45.nTwo]; positivity

/-- The square-root splitting, with the total mass supplied as a hypothesis. -/
lemma sqrt_add_sqrt_le_of_sum {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B = 2 * π * Sec45.nTwo) :
    sqrt A + sqrt B ≤ 2 * sqrt π * sqrt Sec45.nTwo := by
  have hsA : sqrt A ^ 2 = A := sq_sqrt hA
  have hsB : sqrt B ^ 2 = B := sq_sqrt hB
  have hsπ : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsN : sqrt Sec45.nTwo ^ 2 = Sec45.nTwo := sq_sqrt nTwo_pos.le
  have hsq : (sqrt A + sqrt B) ^ 2 = A + B + 2 * (sqrt A * sqrt B) := by
    rw [sq]; linarith
  have hprod : 2 * (sqrt A * sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (sqrt A - sqrt B)]
  have hR : (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 = 4 * π * Sec45.nTwo := by
    nlinarith [hsπ, hsN]
  have hkey : (sqrt A + sqrt B) ^ 2 ≤ (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 := by
    rw [hsq, hR]; linarith
  have h0 : 0 ≤ sqrt A + sqrt B := by positivity
  have h2 : 0 ≤ 2 * sqrt π * sqrt Sec45.nTwo := by positivity
  nlinarith [hkey, h0, h2, sq_nonneg (sqrt A + sqrt B - 2 * sqrt π * sqrt Sec45.nTwo),
    mul_nonneg h0 h2]


/-! ### Round 2 split of the sampling leaf

Copied from the lab files Decomp431a and Sampling431, which import Decomp389b and so sit
downstream. The two signed raw leaves of Decomp431a are merged here into one leaf
signed_sampling_raw with a sign ε equal to 1 or −1, so that the sorry of
middle_sampling_bound is replaced one for one. The scalar weight bounds are PROVED copies. -/

/-- The signed middle zero contribution, zeros with ε Im ρ above 1, book pages 433 and 434. -/
noncomputable def signedMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T ε : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | 1 < ε * ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- PROVED. The middle range is the disjoint union of its two signed halves.
Copy of Decomp431a.middle_mass_signed_split; summability now from the finiteness of the
strip zeros, so the zero hypothesis is not needed. -/
theorem middle_mass_signed_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    middleMass χ δ T = signedMass χ δ T 1 + signedMass χ δ T (-1) := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) :=
    ZeroCount1623.summable_zeroIdx χ T _
  unfold signedMass middleMass
  rw [← (hm.indicator _).tsum_add (hm.indicator _)]
  apply tsum_congr
  intro ρ
  by_cases hp : 1 < ρ.val.im
  · have hn : ¬1 < -ρ.val.im := by linarith
    have ha : ¬|ρ.val.im| ≤ 1 := by
      intro ha
      have hh := (abs_le.mp ha).2
      linarith
    simp [Set.indicator, hp, hn, ha]
  · by_cases hn : 1 < -ρ.val.im
    · have ha : ¬|ρ.val.im| ≤ 1 := by
        intro ha
        have hh := (abs_le.mp ha).1
        linarith
      simp [Set.indicator, hp, hn, ha]
    · have ha : |ρ.val.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [Set.indicator, hp, hn, ha]

/-- PROVED. log 2π is above 1.69, from 2π above 6 and log 3 above 1. -/
lemma log_two_pi_gt_169 : (1.69 : ℝ) < log (2 * π) := by
  have h6 : log 6 ≤ log (2 * π) := log_le_log (by norm_num) (by linarith [pi_gt_three])
  have h3 : 1 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    linarith [exp_one_lt_d9]
  have h2 := log_two_gt_d9
  have h23 : log 6 = log 2 + log 3 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  linarith

/-- PROVED. Copy of Sampling431.hasDerivAt_log_weight_primitive, book page 434. -/
theorem hasDerivAt_log_weight_primitive (a b q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => u * ((a * log (q * u) + b) ^ 2 -
        2 * a * (a * log (q * u) + b) + 2 * a ^ 2))
      ((a * log (q * t) + b) ^ 2) t := by
  have hl := (Real.hasDerivAt_log (mul_ne_zero hq.ne' ht.ne')).comp t
    ((hasDerivAt_id t).const_mul q)
  have hw := (hl.const_mul a).add_const b
  have hp := (hasDerivAt_id t).mul
    (((hw.pow 2).sub (hw.const_mul (2 * a))).add_const (2 * a ^ 2))
  convert hp using 1
  · rfl
  · simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ; ring

/-- PROVED. Copy of Sampling431.integral_log_weight_sq, book page 434. -/
theorem integral_log_weight_sq (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) =
      T * ((a * log (q * T) + b) ^ 2 - 2 * a * (a * log (q * T) + b) + 2 * a ^ 2) -
      ((a * log q + b) ^ 2 - 2 * a * (a * log q + b) + 2 * a ^ 2) := by
  have hc : ContinuousOn (fun t : ℝ => (a * log (q * t) + b) ^ 2) (Set.uIcc 1 T) := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    fun_prop (disch := positivity)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_log_weight_primitive a b q t hq
      (lt_of_lt_of_le zero_lt_one ((Set.uIcc_of_le hT ▸ ht).1))) hc.intervalIntegrable
  simpa only [one_mul, mul_one] using hh

/-- PROVED. Copy of Sampling431.integral_log_weight_sq_le. -/
theorem integral_log_weight_sq_le (a b q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T, (a * log (q * t) + b) ^ 2) ≤
      T * ((a * log (q * T) + b - a) ^ 2 + a ^ 2) := by
  rw [integral_log_weight_sq a b q T hq hT]
  nlinarith [sq_nonneg (a * log q + b - a), sq_nonneg a]

/-- PROVED. Copy of Sampling431.error_weight_root_bound, the coefficient 3.242 of page 434. -/
theorem error_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, (0.15 * log (q * t) + 3.389) ^ 2) ≤
      (0.15 * log (q * T) + 3.242) * sqrt T := by
  have hT0 : 0 ≤ T := by linarith
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hlog : (3.5 : ℝ) ≤ log (q * T) := by linarith [log_two_pi_gt_169]
  have hcoef : (0.15 * log (q * T) + 3.389 - 0.15) ^ 2 + 0.15 ^ 2 ≤
      (0.15 * log (q * T) + 3.242) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 0.15 3.389 q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by linarith) (sqrt_nonneg T), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0, mul_comm] using hbudget

/-- PROVED. Copy of Sampling431.main_weight_root_bound, page 434 before display 16.26. -/
theorem main_weight_root_bound (q T : ℝ) (hq : 0 < q) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ q * T) :
    sqrt (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) ≤
      sqrt T * log (q * T / (2 * π * sqrt (exp 1))) := by
  have hT0 : 0 ≤ T := by linarith
  have hqT0 : 0 < q * T := mul_pos hq (by linarith)
  have hl := log_le_log (by positivity : (0 : ℝ) < 2 * π * exp 2) hlarge
  rw [log_mul (by positivity : (2 * π : ℝ) ≠ 0) (exp_ne_zero 2), log_exp] at hl
  have hL : (2 : ℝ) ≤ log (q * T) - log (2 * π) := by linarith
  have hshift : log (q * T / (2 * π * sqrt (exp 1))) =
      log (q * T) - log (2 * π) - 1 / 2 := by
    rw [log_div hqT0.ne' (by positivity),
      log_mul (by positivity : (2 * π : ℝ) ≠ 0) (by positivity : sqrt (exp 1) ≠ 0),
      log_sqrt (exp_pos 1).le, log_exp]
    ring
  have heq : (∫ t in (1 : ℝ)..T, log (q * t / (2 * π)) ^ 2) =
      ∫ t in (1 : ℝ)..T, (1 * log (q * t) + -log (2 * π)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [log_div (mul_ne_zero hq.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
      (by positivity)]
    ring
  have hcoef : (1 * log (q * T) + -log (2 * π) - 1) ^ 2 + 1 ^ 2 ≤
      (log (q * T) - log (2 * π) - 1 / 2) ^ 2 := by nlinarith
  have hbudget := (integral_log_weight_sq_le 1 (-log (2 * π)) q T hq hT).trans
    (mul_le_mul_of_nonneg_left hcoef hT0)
  rw [heq, hshift]
  apply (sqrt_le_iff).mpr
  refine ⟨mul_nonneg (sqrt_nonneg T) (by linarith), ?_⟩
  simpa only [mul_pow, sq_sqrt hT0] using hbudget

/-- LEAF. Book page 434, the first Plancherel estimate after display 16.26.
The Gaussian square moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_line_energy_bound (δ : ℝ) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  have hsum := line_integral_sum δ
  have h1 : lineEnergy δ 1 = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  have h2 : lineEnergy δ (-1) = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  rw [h1, h2]
  exact sqrt_add_sqrt_le_of_sum (by positivity) (by positivity) hsum

open Filter Asymptotics

/-- The Gaussian-character integrand of `gaussianMellin`, as a function of one variable. -/
private lemma gauss_cont (δ : ℝ) :
    Continuous (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) := by
  unfold e
  fun_prop

/-- Super-polynomial decay of the Gaussian at infinity. -/
private lemma gauss_isBigO_top (δ : ℝ) :
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
private lemma gauss_isBigO_bot (δ : ℝ) {b : ℝ} (hb : 0 < b) :
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
private lemma gauss_mellin_hasDerivAt (δ : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun x : ℝ => (Real.log x : ℂ) * ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s) s := by
  have hfc : LocallyIntegrableOn (fun x : ℝ => ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
      (Set.Ioi 0) :=
    (gauss_cont δ).locallyIntegrable.locallyIntegrableOn _
  exact (mellin_hasDerivAt_of_isBigO_rpow hfc (gauss_isBigO_top δ) hs1
    (gauss_isBigO_bot δ (by linarith : (0:ℝ) < s.re / 2)) (by linarith)).2

/-- The log-coordinate profile of the derivative of the Gaussian Mellin transform. -/
private lemma weighted_cont (δ : ℝ) :
    Continuous (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  unfold e
  fun_prop

/-- The Mellin transform of the log-weighted Gaussian-character integrand on the critical line is
the Fourier integral of its log-coordinate transform. -/
private lemma mellin_log_eq_fourier (δ t : ℝ) :
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
private lemma weighted_norm (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = |u| * (exp (u / 2) * exp (-(exp u) ^ 2 / 2)) := by
  rw [norm_mul, log_norm, Complex.norm_real, Real.norm_eq_abs]

/-- Pointwise square norm of the log-coordinate derivative profile. -/
private lemma weighted_norm_sq (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = u ^ 2 * (exp u * exp (-(exp u) ^ 2)) := by
  rw [weighted_norm, mul_pow, mul_pow, sq_abs]
  congr 1
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

/-- The log-coordinate derivative profile is dominated by a decaying exponential. -/
private lemma weighted_le (δ : ℝ) (u : ℝ) :
    ‖(u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤
      4 * exp (-(1 / 4 : ℝ) * |u|) := by
  rw [weighted_norm]
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
private lemma weighted_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) := by
  refine Integrable.mono' ((integrable_exp_neg_abs_mul (c := 1 / 4) (by norm_num)).const_mul 4)
    (weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact weighted_le δ u

/-- The log-coordinate derivative profile lies in `L2`. -/
private lemma weighted_memLp (δ : ℝ) :
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
  refine MemLp.mono' hg (weighted_cont δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact weighted_le δ u

/-- The `L2` mass of the log-coordinate derivative profile is the log squared Gaussian moment. -/
private lemma weighted_sq_integral (δ : ℝ) :
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
    rw [weighted_norm_sq, Real.log_exp, smul_eq_mul]
    ring]
  rw [← himg]
  exact LeanLab.HelfgottMajor.MiddleEnergy123.LogMoment431.gaussian_log_square_integral

/-- The Fourier profile of the derivative has integrable square. -/
private lemma integrable_fourier_sq_weighted (δ : ℝ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) := by
  have h2 := weighted_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (weighted_integrable δ)
    (weighted_memLp δ)] with ξ hξ
  rw [hξ]

/-- The Fourier side square integral of the derivative profile. -/
private lemma fourier_sq_integral_weighted (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) y‖ ^ 2 = Sec45.nLog := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (weighted_integrable δ) (weighted_memLp δ)]
  exact weighted_sq_integral δ

/-- The pointwise critical-line identity for the derivative. -/
private lemma deriv_mellin_sq_pointwise (δ t : ℝ) :
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
  have hre : ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re = (1 / 2 : ℝ) := by simp
  rw [(gauss_mellin_hasDerivAt δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      (by rw [hre]; norm_num) (by rw [hre]; norm_num)).deriv, mellin_log_eq_fourier δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

/-- The derivative of the Gaussian Mellin transform has integrable square on the critical line. -/
private lemma integrable_deriv_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
      ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) ξ‖ ^ 2) hR).mpr
      (integrable_fourier_sq_weighted δ)
  refine h.congr ?_
  filter_upwards with t
  exact (deriv_mellin_sq_pointwise δ t).symm

/-- Differentiated Mellin Plancherel on the whole critical line. -/
private lemma integral_deriv_mellin_sq (δ : ℝ) :
    ∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nLog := by
  rw [show (∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, ‖𝓕 (fun u : ℝ => (u : ℂ) * ((exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) (-(1 / (2 * π)) * t)‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with t
    exact deriv_mellin_sq_pointwise δ t]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖𝓕 (fun u : ℝ => (u : ℂ) *
    ((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) y‖ ^ 2)]
  rw [fourier_sq_integral_weighted δ]
  have hcoef : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_div, div_one, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef, smul_eq_mul]

/-- The square-root splitting with an upper bound on the total mass. -/
private lemma sqrt_add_sqrt_le_of_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B ≤ 2 * π * Sec45.nLog) :
    sqrt A + sqrt B ≤ 2 * sqrt π * sqrt Sec45.nLog := by
  have hsA : sqrt A ^ 2 = A := sq_sqrt hA
  have hsB : sqrt B ^ 2 = B := sq_sqrt hB
  have hsπ : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsN : sqrt Sec45.nLog ^ 2 = Sec45.nLog := sq_sqrt Sec45.nLog_nonneg
  have hsq : (sqrt A + sqrt B) ^ 2 = A + B + 2 * (sqrt A * sqrt B) := by
    rw [sq]; linarith
  have hprod : 2 * (sqrt A * sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (sqrt A - sqrt B)]
  have hR : (2 * sqrt π * sqrt Sec45.nLog) ^ 2 = 4 * π * Sec45.nLog := by
    nlinarith [hsπ, hsN]
  have hkey : (sqrt A + sqrt B) ^ 2 ≤ (2 * sqrt π * sqrt Sec45.nLog) ^ 2 := by
    rw [hsq, hR]; linarith
  have h0 : 0 ≤ sqrt A + sqrt B := by positivity
  have h2 : 0 ≤ 2 * sqrt π * sqrt Sec45.nLog := by positivity
  nlinarith [hkey, h0, h2, sq_nonneg (sqrt A + sqrt B - 2 * sqrt π * sqrt Sec45.nLog),
    mul_nonneg h0 h2]

/-- LEAF. Book page 434, the differentiated Mellin Plancherel estimate.
The Gaussian log squared moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_derivative_energy_bound (δ : ℝ) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  have hA : derivativeEnergy δ 1 = ∫ t in Set.Ioi (1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [one_mul]
  have himg : Neg.neg '' (Set.Ioi (1 : ℝ)) = Set.Iio (-1 : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨-x, by linarith, by ring⟩
  have hsub : ∫ t in Set.Ioi (1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t) : ℝ) * Complex.I)‖ ^ 2
      = ∫ t in Set.Iio (-1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      (fun x _ y _ hxy => neg_injective hxy)]
    simp
  have hB : derivativeEnergy δ (-1) = ∫ t in Set.Iio (-1 : ℝ),
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [show derivativeEnergy δ (-1) = ∫ t in Set.Ioi (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((-t) : ℝ) * Complex.I)‖ ^ 2 from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [neg_one_mul]]
    exact hsub
  have hInt : Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
    integrable_deriv_mellin_sq δ
  have hsplit : (∫ t in Set.Ioi (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      + (∫ t in (Set.Ioi (1 : ℝ))ᶜ,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 :=
    integral_add_compl (μ := volume) measurableSet_Ioi hInt
  rw [Set.compl_Ioi] at hsplit
  have hmono : ∫ t in Set.Iio (-1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      ≤ ∫ t in Set.Iic (1 : ℝ),
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    refine setIntegral_mono_set hInt.integrableOn ?_ ?_
    · filter_upwards with t using (by positivity)
    · filter_upwards with t ht
      simp only [Set.mem_Iio, Set.mem_Iic] at ht ⊢
      linarith
  have hFint : ∫ t : ℝ,
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nLog := integral_deriv_mellin_sq δ
  have hsum : derivativeEnergy δ 1 + derivativeEnergy δ (-1) ≤ 2 * π * Sec45.nLog := by
    calc derivativeEnergy δ 1 + derivativeEnergy δ (-1)
        = (∫ t in Set.Ioi (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
          + (∫ t in Set.Iio (-1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
          rw [hA, hB]
      _ ≤ (∫ t in Set.Ioi (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
          + (∫ t in Set.Iic (1 : ℝ),
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
          add_le_add (le_refl _) hmono
      _ = ∫ t : ℝ,
            ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := hsplit
      _ = 2 * π * Sec45.nLog := hFint
  have hAnn : 0 ≤ derivativeEnergy δ 1 := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioi (fun t _ => by positivity)
  have hBnn : 0 ≤ derivativeEnergy δ (-1) := by
    rw [hB]
    exact setIntegral_nonneg measurableSet_Iio (fun t _ => by positivity)
  exact sqrt_add_sqrt_le_of_le hAnn hBnn hsum

/-- The book coefficients of Lemma 16.10 are below the older page 40 coefficients.
Only arithmetic is asserted. No zero sampling input is used.
-/
theorem book_coefficients_le :
    sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog ≤
      sqrt Sec45.nTwo + sqrt Sec45.nLog ∧
    6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo ≤
      17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hs1 : (1 : ℝ) ≤ sqrt π := by linarith [Sec45.sqrt_pi_gt]
  have hs2 : sqrt π ≤ (2 : ℝ) := by linarith [Sec45.sqrt_pi_lt]
  have hs0 : 0 < sqrt π := by positivity
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  obtain ⟨hC0, hC⟩ := BookP1617.K_bds
  have hCpos : 0 ≤ log (2 * π * sqrt (exp 1)) := by linarith
  have hprod0 : 0 ≤ log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := mul_nonneg hCpos hN0
  have hLge : (0.8 : ℝ) ≤ sqrt Sec45.nLog := by
    have hh := Decomp389c.middle_constant_ge
    linarith
  have hprod : log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo ≤ 2.3378771 * 0.941397 :=
    mul_le_mul hC.le Sec45.sqrt_nTwo_lt.le hN0 (by norm_num)
  constructor
  · have hdiv : sqrt Sec45.nTwo / sqrt π ≤ sqrt Sec45.nTwo := by
      rw [div_le_iff₀ hs0]
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hs1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]
  · have hnonneg : 0 ≤ log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]

/-- The large qT branch follows from independent sampling and energy inputs.
CONDITIONAL ON those explicit inputs. Book pages 433 and 434.
-/
theorem large_middle_bound_of_inputs (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hsampling : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389))
    (henergy : sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo)
    (hderiv : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have hsπ : 0 < sqrt π := by positivity
  have hsT := sqrt_nonneg T
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hC : 0 < 2 * π * sqrt (exp 1) := by positivity
  have he : sqrt (exp 1) ≤ exp 2 := by
    have hs : sqrt (exp 1) ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num, by linarith [exp_one_lt_three]⟩
    have hh : (2 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    exact hs.trans hh
  have hshift : 0 ≤ log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) := by
    apply log_nonneg
    rw [le_div_iff₀ hC]
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * π)
    nlinarith
  have hE : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      sqrt Sec45.nTwo / sqrt π := by
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right henergy (by positivity)
      _ = _ := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
  have hp := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) + Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hn := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) - Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hmain : middleMass χ δ T ≤
      (sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      (6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.3 * log (q : ℝ) + 6.778) := by
    calc
      _ ≤ sqrt Sec45.nTwo / sqrt π * sqrt T *
          log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
          (2 * sqrt π * sqrt Sec45.nLog) * (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
          (2 * 2.15581) * (0.15 * log (q : ℝ) + 3.389) := by
        apply hsampling.trans
        gcongr <;> linarith
      _ = _ := by
        rw [log_div hqT0.ne' hC.ne']
        ring
  obtain ⟨hA, hB⟩ := book_coefficients_le
  have ha := mul_le_mul_of_nonneg_right hA (mul_nonneg hsT hlog)
  have hb := mul_le_mul_of_nonneg_right hB hsT
  nlinarith

end LeanLab.HelfgottMajor.MiddleEnergy123.Decomp389b
