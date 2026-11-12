import LeanLab.HelfgottMajor.Decomp457a
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
Split of `principal_contour_identity` in `Decomp457a.lean`.

The one identity of the target combines four analytic steps.  This file cuts it along
exactly those steps, each carried on its own vertical contour, in the sign convention of
the logarithmic derivative, which is minus the Dirichlet series of the weighted von
Mangoldt sum:

1. the weighted prime sum is minus the vertical integral at real part two of the
   logarithmic derivative of the L-function against the shifted Gaussian transform and
   the scale factor (Dirichlet series to contour);
2. moving that line from real part two down to real part minus one half, in one step as
   P0014 Lemma 4.1 does at page 33 display 4.7, crosses the pole at one, whose residue is
   minus the main term, every nontrivial zero, which gives the two zero sums split at the
   height `T`, and the pole at zero, which gives log of two pi; the main term exists only
   at conductor one, which is the branching guard;
3. retired by U-1648: the first cut stopped at real part one half, which is not a contour,
   since the logarithmic derivative has a non integrable pole at every zero on that line;
4. at conductor one the L-function is the Riemann zeta function, so that last contour is
   the principal contour of the target.

Each leaf is one of those steps, so no leaf restates the target; the assembly at the end
chains the three live leaves and its own argument is rewriting and ring only.

Degenerate values.  Every contour below is an integral over all of `ℝ` on a line at real
part two or minus one half, where the integrand is continuous, so the integration variable
never divides.  The only division is the
fixed factor `1 / (2 * π)`, and `2 * π` is not zero.  The branching term `if q = 1` is
kept verbatim in every statement that has it, so it is the main term at `q = 1` and zero
otherwise.  At `δ = 0` the shift term `-δ` is `0`, the transform is the plain Gaussian and
the height hypothesis `max (4 * π ^ 2 * |δ|) 100 ≤ T` reads `100 ≤ T`, so no leaf
degenerates at the unshifted frequency.  The scale hypothesis is only `1 ≤ x`, so the
admissible range is `x ≥ 1`: no negative and no zero scale occurs, every power
`(x : ℂ) ^ s` is taken at positive base, and at `x = 1` the scale factor is `1` unless the
exponent is `0`.
-/

namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

/-- LEAF. Step one, the Dirichlet series as a contour integral.  The weighted prime sum
`Schi` is minus the vertical integral at real part two of the logarithmic derivative of
the L-function times the shifted Gaussian transform times the scale factor.  The line at
real part two lies in the half plane of absolute convergence, no zero of the L-function
lies on it, and this step moves no contour: it only writes the sum as an integral. -/
theorem principal_prime_sum_mellin_contour (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Schi etaHeart χ δ x =
      -((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)) := by
  sorry

/-- LEAF. Step two, the whole contour shift, P0014 Lemma 4.1, page 33 display 4.7, at
conductor one.  Moving the vertical line from real part two down to real part minus one
half crosses the pole at one, whose residue is minus the main term, which is the guarded
term; every nontrivial zero with its analytic multiplicity, which gives the two zero sums
split at the height `T` with the plus sign they carry in the target; and the pole at zero,
where the logarithmic derivative of zeta is log of two pi and the continued transform has
residue one.  No zero hypothesis is needed: the two zero sums together run over every zero
in the strip.  U-1648 replaced the former leaves `principal_contour_line_shift_pole_at_one`
and `principal_contour_zero_band_crossing` by this one; both were false, since their line
at real part one half meets zeros of zeta, the integrand is not integrable there and the
Lean integral on that line is zero. -/
theorem principal_contour_shift_two_to_minus_half (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  sorry

/-- LEAF. Step four, the conductor one identification.  At conductor one the character is
the trivial one and its L-function is the Riemann zeta function, so the contour at real
part minus one half written with the L-function is literally the principal contour of the
target, which is written with the zeta function.  This step is a naming step: no contour
moves and no sum occurs. -/
theorem principal_contour_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : q = 1) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) =
      principalContour δ x := by
  subst hq
  unfold principalContour
  congr 1
  congr
  funext t
  congr 2
  have h_triv : χ = 1 := Subsingleton.elim χ 1
  rw [h_triv, DirichletCharacter.LFunction_modOne_eq]

/-- The conductor one contour identity, assembled from the four steps above by rewriting
and ring only.  The target statement is unchanged; the assembly has no sorry of its own
and does not use the target theorem.  Since U-1648 it chains three leaves, and its binders
`hχ`, `hT` and `hzeros` are kept only so that its type stays the target's. -/
theorem principal_contour_identity_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T =
        -(log (2 * π) : ℂ) - principalContour δ x := by
  let A : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
      gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)
  let C : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
      continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)
  have hA : A = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
        gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) := rfl
  have hC : C = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := rfl
  have h1 := principal_prime_sum_mellin_contour x hx q χ δ
  have h2 := principal_contour_shift_two_to_minus_half x hx q χ δ T hq
  have h4 := principal_contour_conductor_one x hx q χ hq δ
  have e1 : Schi etaHeart χ δ x = -A := by
    rw [hA]; exact h1
  have e2 : A = C + (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
      (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
    rw [hA, hC]; exact h2
  have e4 : C = principalContour δ x := by
    rw [hC]; exact h4
  rw [e1, e2, e4]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_identity_split
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_conductor_one
