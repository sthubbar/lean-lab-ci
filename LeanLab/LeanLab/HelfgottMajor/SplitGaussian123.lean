import LeanLab.HelfgottMajor.Lemma41Terms
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottMajor.TailIntegral123
import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.HalfMoment389
import LeanLab.HelfgottMajor.Sec45
import LeanLab.HelfgottMajor.Residue123
import LeanLab.HelfgottMajor.MiddleEnergy123
import LeanLab.HelfgottMajor.SamplingSplit123
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order

/-!
Route burst 2026-11-12, split of Decomp123.gaussian_explicit_estimate.
P0014 Proposition 4.6, pages 43 and 44, display 4.43, with the recorded factor 6 repair.
The proof of Proposition 4.6 applies Lemma 4.1, the explicit formula with residue R,
then Lemma 4.4 to the zeros up to T and Lemma 4.5 to the zeros above T.
This file mirrors the decomposition of Decomp269a, which cannot be imported by Decomp123
because it imports Decomp123 itself. The three analytic pieces stay OPEN with sorry.
Lemma 4.1 is used in corrected form, see the section on Lemma 4.1 below.
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

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count only. P0014 Lemma 4.4, pages 39 and 40,
display 4.32 and the final Cauchy Schwarz step, with the norms of display 4.42 on page 43, in the
book form of Part IV pages 433 and 434: the zeros with 1 < abs Im rho at most T. Same statement
as Decomp269b.middle_mass_bound. Route burst p4 proves it in SamplingSplit123, which keeps the
boundary term at the cutoff T that printed display 16.26 drops, a recorded QUESTION. -/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  exact SamplingSplit123.middle_mass_bound q χ hχ δ T hT hzeros

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count only. The middle mass bound with two
units of slack, for T at least 100. The proof of SamplingSplit123.middle_mass_bound gives the
constant 2.15581 (0.3 log q + 6.778) + 2.15581 (0.3 log qT + 6.778) before it is relaxed to
2.15581 (0.5 log q + 17.7), and the coefficient gap 0.647 on sqrt T log qT pays for the
0.3 log qT term, so 2.15581 times 4.1, about 8.8, is free. Two units of it are kept here to
absorb the log x of the corrected Lemma 4.1 residue. Not a printed statement of P0014. -/
theorem middle_mass_bound_slack (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT100 : 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) - 2 := by
  have hT : 1 ≤ T := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T := by
    have he : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    have h1 := exp_one_lt_three
    have h0 := exp_pos 1
    have hπ := pi_lt_d2
    have he9 : exp 2 ≤ 9 := by rw [he]; nlinarith
    have hqT : (100 : ℝ) ≤ (q : ℝ) * T := by nlinarith
    nlinarith [pi_pos, exp_pos 2]
  have hsπ : 0 < sqrt π := by positivity
  have hsT : 1 ≤ sqrt T := by
    rw [show (1 : ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hT
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
  have henergy := MiddleEnergy123.Decomp389b.gaussian_line_energy_bound δ
  have hderiv := MiddleEnergy123.Decomp389b.gaussian_derivative_energy_bound δ
  have hE : (sqrt (MiddleEnergy123.Decomp389b.lineEnergy δ 1) +
      sqrt (MiddleEnergy123.Decomp389b.lineEnergy δ (-1))) / (2 * π) ≤
      sqrt Sec45.nTwo / sqrt π := by
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right henergy (by positivity)
      _ = _ := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
  have hp := SamplingSplit123.signed_sampling_bound_cutoff q χ hχ δ T 1 (Or.inl rfl) hT
    hlarge hzeros
  have hn := SamplingSplit123.signed_sampling_bound_cutoff q χ hχ δ T (-1) (Or.inr rfl) hT
    hlarge hzeros
  have hsum : MiddleEnergy123.Decomp269b.middleMass χ δ T ≤
      (sqrt (MiddleEnergy123.Decomp389b.lineEnergy δ 1) +
        sqrt (MiddleEnergy123.Decomp389b.lineEnergy δ (-1))) / (2 * π) * (sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1)))) +
      (sqrt (MiddleEnergy123.Decomp389b.derivativeEnergy δ 1) +
        sqrt (MiddleEnergy123.Decomp389b.derivativeEnergy δ (-1))) *
        ((0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T) +
      2 * 2.15581 * (0.15 * log (q : ℝ) + 3.389) +
      2 * 2.15581 * (0.15 * log ((q : ℝ) * T) + 3.389) := by
    rw [MiddleEnergy123.Decomp389b.middle_mass_signed_split χ δ T]
    calc
      _ ≤ _ := add_le_add hp hn
      _ = _ := by ring
  have hX : 0 ≤ sqrt T * log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) :=
    mul_nonneg (by linarith) hshift
  have hY : 0 ≤ (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T :=
    mul_nonneg (by linarith) (by linarith)
  have hmain : MiddleEnergy123.Decomp269b.middleMass χ δ T ≤
      (sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog) * (sqrt T * log ((q : ℝ) * T)) +
      (6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.3 * log (q : ℝ) + 6.778) +
      2.15581 * (0.3 * log ((q : ℝ) * T) + 6.778) := by
    have h1 := mul_le_mul_of_nonneg_right hE hX
    have h2 := mul_le_mul_of_nonneg_right hderiv hY
    have hld : log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) =
        log ((q : ℝ) * T) - log (2 * π * sqrt (exp 1)) := log_div hqT0.ne' hC.ne'
    rw [hld] at h1 hsum
    refine (hsum.trans (add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl)).trans
      (le_of_eq ?_)
    ring
  obtain ⟨_, hB⟩ := MiddleEnergy123.Decomp389b.book_coefficients_le
  have hgap := SamplingSplit123.coefficient_gap
  have hrl : 0 ≤ sqrt T * log ((q : ℝ) * T) := mul_nonneg (by linarith) hlog
  have ha := mul_le_mul_of_nonneg_right hgap hrl
  have hb := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ sqrt T)
  have hc : log ((q : ℝ) * T) ≤ sqrt T * log ((q : ℝ) * T) := by nlinarith
  have key : MiddleEnergy123.Decomp269b.middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log (q : ℝ) + 17.7) - 2 := by
    nlinarith
  exact key

/-- The right side of display 3.4 on page 10 for k equal to 0, without the constant c0. -/
noncomputable def corEnvelope (δ τ : ℝ) : ℝ :=
  if |τ| < 3 / 2 * (π * δ) ^ 2 then exp (-0.1065 * (τ / (π * δ)) ^ 2)
  else exp (-0.1598 * |τ|)

/-- LEAF: P0014 Corollary 3.2, page 10, display 3.4 with k equal to 0 and c0 equal to 4.226:
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

/-- LEAF: P0014 Lemma 4.5, page 41, displays 4.33 to 4.35, the zero sum step, CONDITIONAL ON
the k equal to 0 case of Corollary 3.2 given as hcor: pairing by the functional equation, then
Lemma 4.3 on pages 37 and 38 with the decreasing remark, sum the envelope against the zero
density. QUESTION, minor, see research/burst-20261112/helfgott.md: display 4.33 pairs rho with
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

/-! ## Route burst session 9 split of Lemma 4.1, 2026-11-12, corrected the same day

explicit_formula_remainder is split as in P0014 pages 31 to 37 and 44: Lemma 4.1 with its
residue R written exactly, up to the O star of c0 in display 4.3; then the bound of display
4.23 on the L'/L part of R. The arithmetic of page 44 is PROVED.

CORRECTION. Display 4.7 on page 33 integrates L'/L(s, χ) G_δ(s) x^s but defines R as the
residue at s = 0 of L'/L(s, χ) G_δ(s), without the factor x^s. For an even primitive χ with
q > 1, L(0, χ) = 0, so L'/L has a simple pole at 0 with residue 1, and G_δ has a simple pole
with residue η(0). The pole of the product is double and the factor x^s = 1 + s log x + ...
adds η(0) log x to the residue. Also the functional equation, display 4.8, relates L(s, χ) to
L(1 - s, χ bar), so the constant term carries L'/L(1, χ bar), the complex conjugate of
L'/L(1, χ); the two differ when χ is complex. The true residue for the Gaussian, η(0) = 1, is
  log 2π                                                       for q = 1,
  log(2π/q) + γ - conj(L'/L(1, χ))                              for χ odd,
  log(2π/q) + γ - conj(L'/L(1, χ)) + log x + c0(G_δ)            for χ even, q > 1,
with c0(G_δ) the constant Laurent coefficient of G_δ at 0, bounded as in display 4.3.
Both points are QUESTIONS about the printed Lemma 4.1, recorded with numerics: scripts under
scratchpad l41, ef.py, characters mod 1, 3, 5 and 7, δ in 0, 0.3, -0.7, x in 20, 300, 3000.
The CODEX task309 QUESTION in PROGRESS.md and LogDeriv309 already had the log x term.
AI wrote this Lean code. Binary Goldbach is open.
-/

section RouteBurst9Lemma41

/-- The part of the residue at s = 0 that does not depend on x, for the Gaussian, where η♥(0)
is 1 as stated on page 44: log 2π for q equal to 1, and log(2π/q) + γ minus the complex
conjugate of L'(1, χ)/L(1, χ) else. The conjugate is L'(1, χ bar)/L(1, χ bar), which is what
the functional equation of display 4.8 gives; display 4.2 on page 31 prints χ. -/
noncomputable def residueMain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  if q = 1 then (log (2 * π) : ℂ) else
    ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
        DirichletCharacter.LFunction χ 1)

open Classical in
/-- The term η♥(0) log x of the residue at the double pole s = 0, present exactly when χ is
even and q is above 1, so that L(0, χ) = 0. Display 4.2 on page 31 does not have it. -/
noncomputable def evenPoleTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0

/-- PROVED. The double pole term has norm at most log x for x at least 1. -/
theorem evenPoleTerm_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hx : 1 ≤ x) : ‖evenPoleTerm χ x‖ ≤ log x := by
  have h0 : 0 ≤ log x := log_nonneg hx
  unfold evenPoleTerm
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  · simpa using h0

/-- LEAF: P0014 Lemma 4.1, page 31, displays 4.1 to 4.3, for the Gaussian as used on page 44,
in CORRECTED form; the printed form is a QUESTION and is false for even primitive χ with q > 1.
R is residueMain plus evenPoleTerm plus an error of norm at most c0 of display 4.3. Changes
against the print: evenPoleTerm, the log x of the double pole at s = 0 that display 4.7 loses,
and the conjugate of L'/L(1, χ) in residueMain, from display 4.8. As printed: the norms of
display 4.42 and the contour error (log q + 6.01)(|η'|₂ + 2π abs δ |η|₂) x^(-1/2), with the
true norms of record F-5032. Numerics and details are in the section comment above. -/
theorem lemma_4_1_gaussian (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ c : ℂ, ‖c‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T +
        (residueMain χ + evenPoleTerm χ x + c)‖ ≤
        (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) / sqrt x := by
  sorry

/-- PROVED, CONDITIONAL ON the LEAF inputs Residue123.lemma_4_2 and Residue123.charSumMax_le.
Display 4.23, page 37, with η♥(0) equal to 1, under the zero hypothesis of Lemma 4.2:
the x independent part of R has norm at most 3 log q + 15.289. The conjugate does not change
the norm. -/
theorem residueMain_bound_of_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖residueMain χ‖ ≤ 3 * log q + 15.289 := by
  unfold residueMain
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, log_one,
      abs_of_nonneg (log_nonneg (by nlinarith [pi_gt_three]))]
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    nlinarith [pi_lt_four]
  · rw [if_neg hq]
    have hconj : ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
        (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
          DirichletCharacter.LFunction χ 1) =
        (starRingEnd ℂ) (((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [hconj, Complex.norm_conj]
    exact Residue123.residue_log_derivative_bound_of_zeros χ hχ hq hzeros

/-- PROVED from lemma_4_1_gaussian, the corrected leaf, and residueMain_bound_of_zeros.
P0014 page 44, with the zero hypothesis up to height T, T at least 100, passed to Lemma 4.2
at height 5/8. The residue budget is the printed 3 log q + 13.347 abs delta + 16.695 plus
log x, the double pole term of the corrected Lemma 4.1. -/
theorem explicit_formula_of_pieces_of_zeros (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hz58 : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2 :=
    fun s h0 h1 h2 h3 => hzeros s h0 h1 h2 (by linarith)
  obtain ⟨c, hc, hE⟩ := lemma_4_1_gaussian x hx q χ hχ δ T hT
  refine ⟨residueMain χ + evenPoleTerm χ x + c, ?_, ?_⟩
  · have h1 := residueMain_bound_of_zeros χ hχ hz58
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    have h3 := evenPoleTerm_norm_le χ x hx
    calc ‖residueMain χ + evenPoleTerm χ x + c‖
        ≤ ‖residueMain χ + evenPoleTerm χ x‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖residueMain χ‖ + ‖evenPoleTerm χ x‖ + ‖c‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith [abs_nonneg δ]
  · refine hE.trans ?_
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl

end RouteBurst9Lemma41

/-- PROVED from the corrected leaf lemma_4_1_gaussian and the Lemma 4.2 inputs.
P0014 Lemma 4.1, pages 31 to 36, displays 4.1 to 4.3 and 4.23, as specialized on page 44 in
the proof of Proposition 4.6, in CORRECTED form: the explicit formula with residue
abs R at most 3 log q + 13.347 abs delta + 16.695 + log x and contour error
(log q + 6.01)(1 + 6 abs delta) x^(-1/2), the factor 6 being the recorded repair F-5032.
The printed budget has no log x; that is the QUESTION recorded at lemma_4_1_gaussian. -/
theorem explicit_formula_remainder (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  -- Route burst session 9: Lemma 4.1 with R of display 4.2, then display 4.23 and page 44.
  -- Route burst session 8 p3: display 4.23 through Lemma 4.2 with its zero hypothesis.
  exact explicit_formula_of_pieces_of_zeros x hx q χ hχ δ T hT hzeros

/-- OPEN. P0014 Lemma 4.4, display 4.29 on page 39, with the norms of display 4.42,
as applied on page 43: the zeros up to T, all on the critical line by hzeros, contribute
(2.337 sqrt T log qT + 21.817 sqrt T + 2.85 log q + 74.38) sqrt x. -/
theorem low_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38) * sqrt x := by
  -- Route burst session 9: split at height 1 as on page 39, then the arithmetic of page 43.
  apply low_zero_bound_of_mass χ δ x T _ (by linarith) hzeros
  rw [mass_split χ δ T]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound q χ hχ δ T hT1 hzeros
  have hm := middle_mass_bound q χ hχ δ T hT1 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. The bound of low_zero_bound with two
units of slack in the coefficient of sqrt x, from middle_mass_bound_slack. The slack is real:
it is the gap between the constant the sampling proof gives and the printed 17.7 of display
4.32. It pays for the log x of the corrected Lemma 4.1, since log x is at most 2 sqrt x. -/
theorem low_zero_bound_slack (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x := by
  apply low_zero_bound_of_mass χ δ x T _ (by linarith) hzeros
  rw [mass_split χ δ T]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound q χ hχ δ T hT1 hzeros
  have hm := middle_mass_bound_slack q χ hχ δ T hT100 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

/-- LEAF: P0014 Lemma 4.5, pages 40 to 43, display 4.35 and its use on page 43:
the zeros above T contribute log(qT/2π)(4.329 e^(-0.1598 T)
+ 0.802 abs delta e^(-0.1065 (T/(π abs delta))^2)) x. -/
theorem high_zero_bound (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  -- Route burst session 9: display 4.35 bound, then displays 4.36 and 4.41, page 42.
  obtain ⟨hs, hm⟩ := tail_mass_integral q χ hχ δ T hT hzeros
  apply high_zero_bound_of_mass χ δ x T _ hx hs
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := TailIntegral123.exp_integral_bound q T hT100
  have hg : TailIntegral123.gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, TailIntegral123.gaussianTailIntegral]
    · exact TailIntegral123.gaussian_integral_bound q δ T hδ hT
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  calc
    _ ≤ 4.226 * (TailIntegral123.expTailIntegral q T +
          TailIntegral123.gaussianTailIntegral q δ T) := hm
    _ ≤ 4.226 * (1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) +
        0.18787 * |δ| * log (q * T / (2 * π)) *
          exp (-0.1065 * (T / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add he hg) (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
        mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
          (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]

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
Lemmas 4.1, 4.4 and 4.5 into display 4.43, written out without Decomp123.gaussianError.
CORRECTED inputs: the residue budget has the log x of the corrected Lemma 4.1, and the low
zero bound comes with two units of slack on sqrt x, see low_zero_bound_slack. The two cancel
because log x is at most 2 sqrt x for x at least 1. The conclusion is display 4.43 as before. -/
theorem assembly_of_components (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x)
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
  have hlogx : log x ≤ 2 * sqrt x := by
    have h := log_le_sub_one_of_pos hs0
    rw [log_sqrt hx0.le] at h
    linarith
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
