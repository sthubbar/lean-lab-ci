import LeanLab.HelfgottMajor.Lemma41Terms
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottMajor.TailIntegral123
import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.HalfMoment389
import LeanLab.HelfgottMajor.Sec45
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order

/-!
Route burst 2026-11-12, split of Decomp123.gaussian_explicit_estimate.
P0014 Proposition 4.6, pages 43 and 44, display 4.43, with the recorded factor 6 repair.
The proof of Proposition 4.6 applies Lemma 4.1, the explicit formula with residue R,
then Lemma 4.4 to the zeros up to T and Lemma 4.5 to the zeros above T.
This file holds the shared development and the five analytic pieces that stay OPEN, each
one a named paper step and marked LEAF in its doc comment: Lemma 4.1 with its residue,
the logarithmic derivative bound of pages 36 and 37, Lemma 4.4 in the range above height
1, Corollary 3.2 at k equal to 0, and Lemma 4.5 as the zero sum step. The three statements
Decomp123 needs are proved from them in SplitGaussian123, which imports this file. The
namespace stays LeanLab.HelfgottMajor.SplitGaussian123, so every name Decomp123 and the
rest of the lab refer to is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- The Mellin transform F_delta used on page 43 in the proof of display 4.43. -/
noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

/-- A zero contribution with its analytic multiplicity, as in display 4.1 on page 31. -/
noncomputable def zeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (ρ : ℂ) : ℂ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ •
    (gaussianMellin δ ρ * (x : ℂ) ^ ρ)

/-- The zero sum over zeros of height at most T, Lemma 4.4, display 4.29 on page 39. -/
noncomputable def lowZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, zeroTerm χ δ x ρ.val

/-- The zero sum over zeros of height above T, Lemma 4.5 on page 40. -/
noncomputable def highZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, zeroTerm χ δ x ρ.val

/-! ## Route burst session 9 split, 2026-11-12

The three open pieces below are split further along P0014. Lemma 4.4 is split at height 1 as on
page 39; its very low range is PROVED from the shared lab zero count ZeroCount1623 and the
Gaussian half moment of display 4.42. Lemma 4.5 is reduced to its zero sum step, displays 4.33
to 4.35, with the integral bounds 4.36 and 4.41 PROVED in TailIntegral123.
These mirror Zeros269, Decomp269b and Decomp269c, which this file cannot import because they
import Decomp123, which imports this file. AI wrote this Lean code. Binary Goldbach is open.
-/

section RouteBurst9
open MeasureTheory

/-- The multiplicity weighted Mellin norm of one zero, P0014 Lemma 4.4 pages 38 and 39 and
Lemma 4.5 page 40. The same definition as Decomp269b.mellinMassTerm. -/
noncomputable def mellinMassTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * ‖gaussianMellin δ ρ‖

/-- PROVED. P0014 display 4.30, page 39: the trivial bound of the Gaussian Mellin transform by
the absolute integral. Copy of Gaussian269.mellin_norm_le. -/
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

/-- PROVED. P0014 display 4.30 on page 39 with the norm 2.15581 of display 4.42 on page 43:
on the critical line the Gaussian Mellin transform has norm at most 2.15581. -/
theorem mellin_critical_norm_le (δ : ℝ) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 := by
  have h := mellin_norm_le δ s
  rw [hs] at h
  exact h.trans HalfMoment389.gaussian_half_moment_bound

/-- PROVED. The critical line gives the square root of x in the proof of Proposition 4.6,
page 43. Copy of Zeros269.zero_term_norm. -/
theorem zero_term_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (hx : 0 < x) (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm χ δ x ρ‖ = mellinMassTerm χ δ ρ * sqrt x := by
  rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ, ← sqrt_eq_rpow, mellinMassTerm]
  ring

/-- PROVED. P0014 page 43, proof of Proposition 4.6: the zeros up to T, all on the critical
line, contribute their Mellin mass times sqrt x. CONDITIONAL ON hzeros and hbudget only.
The index set is finite by ZeroCount1623.stripZeros_finite, with no hypothesis. -/
theorem low_zero_bound_of_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T B : ℝ) (hx : 0 < x)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) ≤ B) :
    ‖lowZeros χ δ x T‖ ≤ B * sqrt x := by
  haveI := ZeroCount1623.zeroIdx_finite χ T
  unfold lowZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm (Summable.of_finite)
    _ = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val * sqrt x := by
      apply tsum_congr
      intro ρ
      exact zero_term_norm χ δ x hx ρ.val
        (hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1 ρ.property.2.2.2)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) * sqrt x :=
      tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (sqrt_nonneg x)

/-- PROVED. P0014 page 43, proof of Proposition 4.6: the zeros above T contribute at most their
Mellin mass times x, since the real part of each zero is below 1 and x is at least 1.
CONDITIONAL ON hsum and hbudget only. Copy of Zeros269.high_zero_bound_of_mellin_sum. -/
theorem high_zero_bound_of_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ x T B : ℝ) (hx : 1 ≤ x)
    (hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val))
    (hbudget : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤ B) :
    ‖highZeros χ δ x T‖ ≤ B * x := by
  have hx0 : 0 < x := by linarith
  have hpoint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ ≤
        mellinMassTerm χ δ ρ.val * x := by
    intro ρ
    rw [zeroTerm, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, mellinMassTerm]
    have hp : x ^ ρ.val.re ≤ x := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx ρ.property.2.2.1.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hz := (hsum.mul_right x).of_norm_bounded hpoint
  unfold highZeros
  calc
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ‖zeroTerm χ δ x ρ.val‖ :=
      norm_tsum_le_tsum_norm hz.norm
    _ ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val * x :=
      hz.norm.tsum_le_tsum hpoint (hsum.mul_right x)
    _ = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) * x := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hx0.le

/-- The part of the low Mellin mass with absolute imaginary part at most 1, P0014 page 39. -/
noncomputable def veryLowMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The part of the low Mellin mass with absolute imaginary part above 1, P0014 pages 39, 40. -/
noncomputable def middleMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- PROVED. The partition at height 1 in the proof of Lemma 4.4, P0014 page 39.
No hypothesis: the index set is finite. -/
theorem mass_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, mellinMassTerm χ δ ρ.val) =
      veryLowMass χ δ T + middleMass χ δ T := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := Summable.of_finite
  unfold veryLowMass middleMass
  rw [← (hm.indicator _).tsum_add (hm.indicator _)]
  apply tsum_congr
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1 <;> simp [Set.indicator, h]

/-- PROVED, CONDITIONAL ON the shared lab leaf ZeroCount1623.book_zero_count.
P0014 page 39, the very low zero paragraph: N(1, χ) is at most 0.819 log q + 16.8 by displays
4.25 and 4.26, and each zero on the critical line has Mellin norm at most 2.15581 by display
4.30 with the norm of display 4.42. Same statement as Decomp269b.very_low_mass_bound. -/
theorem very_low_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  classical
  haveI := ZeroCount1623.zeroIdx_finite χ T
  have hc := ZeroCount1623.very_low_count χ hχ T hT
  calc
    veryLowMass χ δ T ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, 2.15581 *
          Set.indicator {ρ : ZeroCount1623.ZeroIdx χ T | |ρ.val.im| ≤ 1}
            (fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ)) ρ := by
      unfold veryLowMass
      apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
      intro ρ
      by_cases h : |ρ.val.im| ≤ 1
      · simp only [Set.indicator, Set.mem_setOf_eq, h, if_true]
        have hre := hzeros ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2.1
          ρ.property.2.2.2
        have hn := mellin_critical_norm_le δ ρ.val hre
        unfold mellinMassTerm
        rw [mul_comm (2.15581 : ℝ)]
        exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
      · simp [Set.indicator, h]
    _ = 2.15581 * ∑' ρ : ZeroCount1623.ZeroIdx χ T,
          Set.indicator {ρ : ZeroCount1623.ZeroIdx χ T | |ρ.val.im| ≤ 1}
            (fun ρ => (ZeroCount1623.mult χ ρ.val : ℝ)) ρ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by norm_num)

/-- LEAF: OPEN. P0014 Lemma 4.4, pages 39 and 40, display 4.32 and the final Cauchy Schwarz step,
with the norms of display 4.42 on page 43: the zeros with 1 < abs Im rho at most T.
Same statement as Decomp269b.middle_mass_bound, whose lab split in Decomp389b is open. -/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  sorry

/-- The right side of display 3.4 on page 10 for k equal to 0, without the constant c0. -/
noncomputable def corEnvelope (δ τ : ℝ) : ℝ :=
  if |τ| < 3 / 2 * (π * δ) ^ 2 then exp (-0.1065 * (τ / (π * δ)) ^ 2)
  else exp (-0.1598 * |τ|)

/-- LEAF: OPEN. P0014 Corollary 3.2, page 10, display 3.4 with k equal to 0 and c0 equal to 4.226:
for s with real part in the closed unit interval and abs Im s at least max(100, 4π² abs δ),
the Mellin transform F_δ of e^(-t²/2) e(δt) satisfies abs F_δ(s) + abs F_δ(1 - s) at most
c0 times the envelope. A statement about the Gaussian alone, with no zeros. It rests on
Theorem 3.1, pages 9 and 10, the saddle point analysis of Section 3. -/
theorem corollary_3_2_k0 (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im := by
  sorry

/-- PROVED. The envelope of display 3.4 is at most the sum of its two nonnegative branches,
the Gaussian branch being absent at zero shift, where the first case of 3.4 is empty. -/
theorem corEnvelope_le (δ τ : ℝ) :
    corEnvelope δ τ ≤ exp (-0.1598 * |τ|) +
      if δ = 0 then 0 else exp (-0.1065 * (|τ| / (π * |δ|)) ^ 2) := by
  unfold corEnvelope
  by_cases hδ : δ = 0
  · subst hδ
    have h : ¬ |τ| < 3 / 2 * (π * 0) ^ 2 := by
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact not_lt.mpr (abs_nonneg τ)
    rw [if_neg h, if_pos rfl, add_zero]
  · have hsq : (τ / (π * δ)) ^ 2 = (|τ| / (π * |δ|)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs, mul_pow, mul_pow, sq_abs]
    rw [ite_cond_eq_false _ _ (eq_false hδ), hsq]
    have h1 := exp_pos (-0.1598 * |τ|)
    have h2 := exp_pos (-0.1065 * (|τ| / (π * |δ|)) ^ 2)
    split_ifs <;> linarith

/-- PROVED, CONDITIONAL ON hcor, the k equal to 0 case of Corollary 3.2 on page 10:
one zero above height T has multiplicity weighted Mellin norm at most 4.226 times its
multiplicity times the envelope, as used in display 4.33 on page 41. -/
theorem zero_mass_le_envelope {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) :
    mellinMassTerm χ δ ρ.val ≤
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (4.226 * corEnvelope δ ρ.val.im) := by
  have hT' : max 100 (4 * π ^ 2 * |δ|) ≤ |ρ.val.im| := by
    rw [max_comm]; exact hT.trans ρ.property.2.2.2.le
  have h := hcor ρ.val ρ.property.2.1.le ρ.property.2.2.1.le hT'
  have hn : ‖gaussianMellin δ ρ.val‖ ≤ 4.226 * corEnvelope δ ρ.val.im := by
    linarith [norm_nonneg (gaussianMellin δ (1 - ρ.val))]
  unfold mellinMassTerm
  exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)

/-- LEAF: OPEN. P0014 Lemma 4.5, page 41, displays 4.33 to 4.35, the zero sum step, CONDITIONAL ON
the k equal to 0 case of Corollary 3.2 given as hcor: pairing by the functional equation, then
Lemma 4.3 on pages 37 and 38 with the decreasing remark, sum the envelope against the zero
density. QUESTION, minor, see build/burst-20261112-helfgott.md in this folder: display 4.33 pairs rho with
1 minus rho, which is a zero of L of s and chi bar, not of L of s and chi, when chi is complex. -/
theorem tail_mass_of_corollary (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) := by
  sorry

/-- PROVED from the two OPEN pieces corollary_3_2_k0 and tail_mass_of_corollary.
P0014 Lemma 4.5, page 41, displays 4.33 to 4.35: the multiplicity weighted Mellin mass of the
zeros above height T is summable and at most 4.226 times the two tail integrals.
Same statement as Decomp269c.tail_mass_integral. -/
theorem tail_mass_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) :=
  tail_mass_of_corollary q χ hχ δ T hT hzeros
    (fun s h0 h1 hτ => corollary_3_2_k0 δ s h0 h1 hτ)

end RouteBurst9

/-! ## Route burst session 9 split of Lemma 4.1, 2026-11-12

explicit_formula_remainder is split as in P0014 pages 31 to 37 and 44: Lemma 4.1 with its
residue R of display 4.2 written exactly, up to the O star of c0 in display 4.3; then the bound
of display 4.23 on the L'/L part of R. The arithmetic of page 44 is PROVED.
AI wrote this Lean code. Binary Goldbach is open.
-/

section RouteBurst9Lemma41

/-- The main part of the residue R of display 4.2, page 31, for the Gaussian, where η♥(0) is 1
as stated on page 44: log 2π for q equal to 1, and log(2π/q) + γ - L'(1, χ)/L(1, χ) else. -/
noncomputable def residueMain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  if q = 1 then (log (2 * π) : ℂ) else
    ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

/-- LEAF: OPEN. P0014 Lemma 4.1, page 31, displays 4.1 to 4.3, for η = η♥ as used on page 44:
the explicit formula holds with R equal to residueMain plus an error of norm at most c0 of
display 4.3, here with the Gaussian norms 1.03045, 1.07791, 2.15581 and 1.03045 of display
4.42, page 43, and with contour error (log q + 6.01)(|η'|₂ + 2π abs δ |η|₂) x^(-1/2), where
|η'|₂ is sqrt(sqrt π / 4) and |η|₂ is sqrt Sec45.nTwo, the true norms of record F-5032.
The sum over all nontrivial zeros is written as lowZeros plus highZeros. -/
theorem lemma_4_1_gaussian (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ c : ℂ, ‖c‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + (residueMain χ + c)‖ ≤
        (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) / sqrt x := by
  sorry

/-- LEAF: OPEN. P0014 pages 36 and 37, displays 4.18 to 4.22 and the display before 4.23:
for χ primitive and nontrivial, abs of log(2π/q) + γ - L'(1, χ)/L(1, χ) is at most
3 log q + 15.289. A statement about L(1, χ) alone, with no zeros. -/
theorem residue_log_derivative_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    ‖((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      3 * log q + 15.289 := by
  sorry

/-- PROVED, CONDITIONAL ON residue_log_derivative_bound. Display 4.23, page 37, with η♥(0)
equal to 1: the main part of R has norm at most 3 log q + 15.289, the trivial character
giving log 2π, which is below 15.289 as the paper notes. -/
theorem residueMain_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖residueMain χ‖ ≤ 3 * log q + 15.289 := by
  unfold residueMain
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, log_one,
      abs_of_nonneg (log_nonneg (by nlinarith [pi_gt_three]))]
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    nlinarith [pi_lt_four]
  · rw [if_neg hq]
    exact residue_log_derivative_bound χ hχ hq

/-- PROVED from lemma_4_1_gaussian and residue_log_derivative_bound. P0014 page 44: with
η♥(0) equal to 1 and the norms of display 4.42, display 4.23 and c0_gauss give
abs R at most 3 log q + 13.347 abs δ + 16.695, and the repaired norm bound
Lemma41Terms.repaired gives the contour factor 1 + 6 abs δ. -/
theorem explicit_formula_of_pieces (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  obtain ⟨c, hc, hE⟩ := lemma_4_1_gaussian x hx q χ hχ δ T hT
  refine ⟨residueMain χ + c, ?_, ?_⟩
  · have h1 := residueMain_bound χ hχ
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    calc ‖residueMain χ + c‖ ≤ ‖residueMain χ‖ + ‖c‖ := norm_add_le _ _
      _ ≤ _ := by linarith [abs_nonneg δ]
  · refine hE.trans ?_
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl

end RouteBurst9Lemma41

/-- PROVED. P0014 page 44, last display of the proof of Proposition 4.6:
(6.01 - 6)(1 + 6 abs delta) + 13.347 abs delta + 16.695 is below 14 abs delta + 17,
so the extra 0.01 of the contour term is absorbed into the residue budget for x at least 1. -/
theorem contour_residue_budget (q δ x : ℝ) (hx : 1 ≤ x) (hδ : 0 ≤ δ) :
    (log q + 6.01) * (1 + 6 * δ) / sqrt x + 3 * log q + 13.347 * δ + 16.695 ≤
      (log q + 6) * (1 + 6 * δ) / sqrt x + 3 * log q + 14 * δ + 17 := by
  have h := div_le_self (show 0 ≤ (0.01 : ℝ) * (1 + 6 * δ) by positivity)
    (one_le_sqrt.mpr hx)
  have hr := Lemma41Terms.repaired_R hδ
  have he : (log q + 6.01) * (1 + 6 * δ) / sqrt x =
      (log q + 6) * (1 + 6 * δ) / sqrt x + 0.01 * (1 + 6 * δ) / sqrt x := by ring
  rw [he]
  linarith

/-- PROVED. P0014 pages 43 and 44, the triangle inequality and arithmetic that combine
Lemmas 4.1, 4.4 and 4.5 into display 4.43, written out without Decomp123.gaussianError. -/
theorem assembly_of_components (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x)
    (hH : ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x := by
  obtain ⟨R, hR, hE⟩ := hformula
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hbudget := contour_residue_budget (q : ℝ) |δ| x hx (abs_nonneg δ)
  have htri : ‖Schi etaHeart χ δ x -
      (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ +
        ‖lowZeros χ δ x T‖ + ‖highZeros χ δ x T‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T + R) -
          lowZeros χ δ x T - highZeros χ δ x T - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  have heq :
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x =
      log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
          sqrt x + (3 * log q + 14 * |δ| + 17) +
        (log q + 6) * (1 + 6 * |δ|) / sqrt x := by
    generalize hroot : sqrt x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    have hsne : s ≠ 0 := by rw [← hroot]; exact hs0.ne'
    rw [hxx]
    field_simp [hsne]
  rw [heq]
  linarith

end LeanLab.HelfgottMajor.SplitGaussian123
