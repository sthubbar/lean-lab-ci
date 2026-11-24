import LeanLab.HelfgottMajor.Gaussian123Base
import LeanLab.HelfgottMajor.MainHyps123
import LeanLab.HelfgottMajor.MainTail123

/-!
Design queue Q1, run 20261124T0803Z-14981, 2026-11-24. P0014, Helfgott, Major arcs for
Goldbach's problem, arXiv 1305.2897v4, Lemma 4.5, page 41, displays 4.33 to 4.35.

The sealed step `SplitGaussian123.tail_mass_of_corollary` is NOT shown false, and no
counterexample is known. Its printed proof fails in two places. The pairing of rho with
1 minus rho in display 4.33 needs chi real, since for complex chi the point 1 minus rho is a
zero of the L function of chi bar. Display 4.35 drops the boundary term f of y times g of y
that comes from the Stieltjes summation after display 4.28 on page 38.

This file restates the step so that a prover can reach it zero by zero for every primitive
chi. Each zero above height T, on either side of the real axis, is bounded by Corollary 3.2
at k equal to 0, given as hcor, with no pairing. The two sided envelope sum is then bounded
by a Stieltjes summation against the two sided count, which is twice the one sided book count
of `ZeroCount1623.bookCount` up to twice `ZeroCount1623.bookError`, by
`MainTail123.zero_count_two_sided_of_book`. That gives the factor 2 on the tail integrals and
a boundary term 4 times the envelope at T times bookError at T. The density
`TailIntegral123.countDensity` carries 1 over 4t, which covers the 0.15 over t that the
derivative of bookError contributes. With the factor 4.226 of hcor the restated bound is
8.452 times the two tail integrals plus 16.904 times the envelope at T times bookError at T.

Numeric screen at q equal to 1, T equal to 200, shift 0, using the 204 zeta zeros with
ordinate between 200 and 520: the two sided envelope sum is 9.4286e-14, twice the integral is
9.1853e-14, so the boundary term is needed; the counting bound with boundary is 3.1244e-13,
ratio 0.302. The true two sided Mellin mass is 3.2149e-69 against the restated bound
1.3204e-12.

Status: `two_sided_envelope_count_le` is the one new LEAF, a sorry. The reduction
`tail_mass_bound_unpaired_of_count` is PROVED from it as a hypothesis. The restated step
`tail_mass_bound_unpaired` is assembled from the two.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DQTailUnpaired
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- The two branch envelope of display 3.4 on page 10 at height t, as a sum of its two
branches. The Gaussian branch is absent at shift 0. This is the bound of
`SplitGaussian123.corEnvelope_le`, evaluated at the cut height T for the boundary term. -/
noncomputable def branchEnv (δ t : ℝ) : ℝ :=
  exp (-0.1598 * |t|) + if δ = 0 then 0 else exp (-0.1065 * (|t| / (π * |δ|)) ^ 2)

/-- PROVED. The two branch envelope is nonnegative. -/
theorem branchEnv_nonneg (δ t : ℝ) : 0 ≤ branchEnv δ t := by
  unfold branchEnv
  have h1 := exp_pos (-0.1598 * |t|)
  split_ifs
  · linarith
  · linarith [exp_pos (-0.1065 * (|t| / (π * |δ|)) ^ 2)]

/-- LEAF: OPEN. The counting step of P0014 Lemma 4.5 on page 41, displays 4.33 to 4.35, done
without the pairing of display 4.33 and with the boundary term that page 38 drops.
CONDITIONAL ON hB, the book zero count of display 4.26 on page 38 in the one sided half
weighted form of book page 431. The sum over all zeros of the L function of chi above
height T on both sides, each weighted by its multiplicity times the two branch envelope, is
at most twice the two tail integrals plus 4 times the envelope at T times bookError at T.
Proof route: the two sided count N of t is within twice bookError of twice bookMain for t at
least 1. Stieltjes summation of the decreasing envelope f gives the sum as minus f of T
times N of T minus the integral of f prime times N. Bound N of T from below and N of t from
above, then integrate the error part by parts: the derivative of bookMain is the log part of
countDensity and the derivative of bookError is 0.15 over t, below the 1 over 4t of
countDensity. The two boundary pieces give 4 times f of T times bookError of T.
Numeric screen at q equal to 1, T equal to 200, shift 0: left side 9.4286e-14, right side
3.1244e-13.
STUCK note, three approaches scoped in this run, none finished in the time box. First,
Mathlib Abel summation `sum_mul_eq_sub_integral_mul` is indexed by natural numbers, while the
zero ordinates are real, so it does not apply without a change of index. Second, the unit
shell split of `tail_envelope_summable_of_shell_count` bounds each shell by its lower end
height, which costs a factor exp of 0.1598 per shell and does not reach the constant 2.
Third, the route that should work: for each zero write f of gamma minus f of U as the
integral of minus f prime from gamma to U, swap the finite sum with the integral via
`MeasureTheory.integral_finset_sum`, which turns it into the integral of minus f prime times
N of t minus N of T, apply `MainTail123.zero_count_two_sided_of_book` pointwise, and let U go
to infinity by monotone convergence. It needs the derivative bounds of both branches and the
integrability already proved in TailIntegral123. Estimated a few hundred lines. -/
theorem two_sided_envelope_count_le (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      2 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * branchEnv δ T * ZeroCount1623.bookError q T := by
  sorry

/-- PROVED, CONDITIONAL ON hB, the book zero count of display 4.26 on page 38, on hcor, the
k equal to 0 case of Corollary 3.2 on page 10, and on hcount, the counting bound of
`two_sided_envelope_count_le` for this character. P0014 Lemma 4.5, page 41, restated
without the pairing of display 4.33: the multiplicity weighted Mellin mass of the zeros above
height T on both sides is summable and at most 8.452 times the two tail integrals plus
16.904 times the envelope at T times bookError at T. Summability comes from the unit shell
count of `MainTail123.tail_shell_count_le_quadratic_of_book`, and the per zero comparison from
`SplitGaussian123.tail_mass_le_two_sided_envelope`. -/
theorem tail_mass_bound_unpaired_of_count (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (hcount : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      2 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * branchEnv δ T * ZeroCount1623.bookError q T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      8.452 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      16.904 * branchEnv δ T * ZeroCount1623.bookError q T := by
  have hT1 : 1 ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hs := tail_envelope_summable_of_shell_count χ δ T (2 * (q : ℝ) + 18) hT1
    (MainTail123.tail_shell_count_le_quadratic_of_book hB χ hχ T)
  obtain ⟨hm, hle⟩ := tail_mass_le_two_sided_envelope χ δ T hT hcor hs
  refine ⟨hm, hle.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 4.226)
  linarith

/-- The restated LEAF of design queue Q1, replacing the bound half of
`SplitGaussian123.tail_mass_of_corollary`. P0014 Lemma 4.5, page 41, displays 4.33 to 4.35,
for every primitive chi, with no pairing and with the boundary term of the Stieltjes
summation. CONDITIONAL ON hB, the book zero count of display 4.26 on page 38, and on hcor,
Corollary 3.2 at k equal to 0 on page 10. Assembled from the PROVED reduction
`tail_mass_bound_unpaired_of_count` and the open counting LEAF
`two_sided_envelope_count_le`, so it depends on that one sorry. -/
theorem tail_mass_bound_unpaired (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      8.452 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      16.904 * branchEnv δ T * ZeroCount1623.bookError q T :=
  tail_mass_bound_unpaired_of_count hB q χ hχ δ T hT hcor
    (two_sided_envelope_count_le hB q χ hχ δ T hT)

end LeanLab.HelfgottMajor.DQTailUnpaired

#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.branchEnv_nonneg
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.two_sided_envelope_count_le
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.tail_mass_bound_unpaired_of_count
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.tail_mass_bound_unpaired
