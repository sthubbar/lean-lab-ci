import LeanLab.HelfgottMajor.Decomp457a

/-!
Split of `principal_contour_identity` in `Decomp457a.lean`.

The one identity of the target combines four analytic steps.  This file cuts it along
exactly those steps, each carried on its own vertical contour, in the sign convention of
the logarithmic derivative, which is minus the Dirichlet series of the weighted von
Mangoldt sum:

1. the weighted prime sum is minus the vertical integral at real part two of the
   logarithmic derivative of the L-function against the shifted Gaussian transform and
   the scale factor (Dirichlet series to contour);
2. moving that line down to real part one half crosses only the pole at one, whose
   residue is minus the main term, so the main term is subtracted there; the main term
   exists only at conductor one, which is the branching guard;
3. moving on, from real part one half down to real part minus one half, crosses the zero
   band sitting at real part one half and the pole at zero, which give the two zero sums
   and log of two pi;
4. at conductor one the L-function is the Riemann zeta function, so that last contour is
   the principal contour of the target.

Each leaf is one of those steps, on its own contour, with the other steps absent, so no
leaf restates the target; the assembly at the end chains the four and its own argument is
rewriting and ring only.

Degenerate values.  Every contour below is an integral over all of `ℝ` of a continuous
complex function, so the integration variable never divides.  The only division is the
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

/-- LEAF. Step two, the pole at one.  Moving the vertical line from real part two down to
real part one half crosses no zero of the L-function, since zeros in the strip lie to the
left of real part one, but it does cross the pole at one.  The residue there is minus the
main term, and the main term is present exactly when the conductor is one, which is the
guarded term.  Nothing here knows about the zeros or about the pole at zero. -/
theorem principal_contour_line_shift_pole_at_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)) -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  sorry

/-- LEAF. Step three, the zero band and the pole at zero.  Moving the line from real part
one half down to real part minus one half crosses the zeros of the L-function in the
strip, which the zero hypothesis puts on real part one half, so the two zero sums with
their analytic multiplicities and Gaussian weights enter with the plus sign they carry in
the target, split at the height `T`.  It also crosses the pole at zero, where the
logarithmic derivative is log of two pi and the continued transform has residue the first
moment; that contributes log of two pi with a plus sign as well. -/
theorem principal_contour_zero_band_crossing (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T := by
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
  sorry

/-- The conductor one contour identity, assembled from the four steps above by rewriting
and ring only.  The target statement is unchanged; the assembly has no sorry of its own
and does not use the target theorem. -/
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
  let B : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + t * Complex.I) *
      gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I)
  let C : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
      continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)
  have hA : A = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
        gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) := rfl
  have hB : B = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((1 / 2 : ℂ) + t * Complex.I) *
        gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I) := rfl
  have hC : C = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := rfl
  have h1 := principal_prime_sum_mellin_contour x hx q χ δ
  have h2 := principal_contour_line_shift_pole_at_one x hx q χ hχ δ
  have h3 := principal_contour_zero_band_crossing x hx q χ hχ δ T hT hzeros
  have h4 := principal_contour_conductor_one x hx q χ hq δ
  have e1 : Schi etaHeart χ δ x = -A := by
    rw [hA]; exact h1
  have e2 : A = B - (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
    rw [hA, hB]; exact h2
  have e3 : B = C + (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T := by
    rw [hB, hC]; exact h3
  have e4 : C = principalContour δ x := by
    rw [hC]; exact h4
  rw [e1, e2, e3, e4]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_identity_split
