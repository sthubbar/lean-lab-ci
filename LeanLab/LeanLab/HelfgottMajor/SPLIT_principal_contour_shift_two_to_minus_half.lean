import LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

/-!
Split of `principal_contour_shift_two_to_minus_half` in
`SPLIT_principal_contour_identity.lean`.

The single identity of the target moves the vertical line of the logarithmic derivative of
the Dirichlet `L`-function from real part two down to real part minus one half, at
conductor one, and it is cut here along the three steps that the move consists of:

1. on the line of real part two the logarithmic derivative is the Dirichlet series of the
   weighted von Mangoldt sum, so the vertical integral on that line is minus the twisted
   prime sum; no contour moves in this step;
2. the move itself, the contour shift of Lemma 4.1 at page 33 display 4.7: it crosses the
   pole at one, whose residue is the conductor one main term, every nontrivial zero of the
   strip, which gives the two zero sums split at the height `T`, and the pole at zero,
   whose residue is log of two pi;
3. at conductor one the character is the trivial one and its `L`-function is the Riemann
   zeta function, so the vertical integral on the line of real part minus one half is the
   principal contour.

A fourth leaf records that the integrand on the line of real part minus one half is
integrable, which is what makes that line an available contour at all; the target asserts
a value for that integral and cannot do so without it.

The assembly at the end chains the three identities, and its own argument is a rewrite and
`ring` only.  It does not use the target theorem, and it does not use the assembly of the
imported split file, which carries the target as an input.

Degenerate values.  The scale hypothesis is only `1 ≤ x`, so no negative and no zero scale
occurs, every power `(x : ℂ) ^ s` is taken at positive base, and at `x = 1` the scale
factor is `1` unless the exponent is `0`.  Every contour below is an integral over all of
`ℝ` on a line at real part two or at real part minus one half; on the second line the
continued Gaussian transform divides by the contour parameter `-1 / 2 + t * I`, whose real
part is `-1 / 2`, so that divisor is never zero and the transform has no junk value there.
The only other division is the fixed factor `1 / (2 * π)`, and `2 * π` is not zero.  The
branching term `if q = 1` is kept verbatim, so it is the main term at `q = 1` and zero
otherwise, and the hypothesis `hq : q = 1` makes the branch taken, never an unsatisfiable
combination.  At `δ = 0` the shift factor `2 * π * I * δ` of the continued transform is
zero and the transformation is the plain Gaussian; nothing in the leaves degenerates there.
The height `T` is unconstrained, and the two zero sets `<|im| ≤ T` and `T < |im|` split the
zeros of the strip for every real `T`, including `T = 0` and negative `T`, where the first
of them is empty and the sum over it is zero.
-/

namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

open scoped ArithmeticFunction

/-! ### A. The line of real part two is the prime sum -/

/-- LEAF. Step one, the line of real part two.  The vertical integral at real part two of
the logarithmic derivative of the `L`-function against the shifted Gaussian transform and
the scale factor is minus the twisted von Mangoldt sum.  The line lies in the half plane of
absolute convergence, no zero of the `L`-function lies on it, and this step moves no
contour: it only writes the prime sum as an integral.  It says nothing about the line of
real part minus one half, about log of two pi, or about either zero sum. -/
theorem principal_two_line_prime_sum (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) = - Schi etaHeart χ δ x := by
  sorry

/-! ### B. The move from real part two to real part minus one half -/

/-- LEAF. Step two, the whole contour shift at conductor one, Lemma 4.1 at page 33 display
4.7.  The twisted prime sum equals minus the principal contour minus log of two pi, plus
the conductor one main term, minus the two zero sums split at the height `T`.  The move
from real part two down to real part minus one half crosses the pole at one, which gives
the guarded main term, every nontrivial zero of the strip with its analytic multiplicity,
which gives the two zero sums, and the pole at zero, which gives log of two pi.  It is one
leg: the intermediate line of real part one half is no contour, since the logarithmic
derivative is not integrable across the zeros of that line, so this step is not cut there.
It asserts no size estimate for the contour and no bound for either zero sum, and it needs
no hypothesis on the location of the zeros. -/
theorem principal_explicit_formula_shift (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    Schi etaHeart χ δ x =
      -((log (2 * π) : ℂ)) - principalContour δ x +
        (if q = 1 then fhat etaHeart (-δ) * x else 0) -
        lowZeros χ δ x T - highZeros χ δ x T := by
  sorry

/-! ### C. The line of real part minus one half at conductor one -/

/-- LEAF. Step three, the conductor one identification.  At conductor one the character is
the trivial one and its `L`-function is the Riemann zeta function, so the vertical integral
at real part minus one half of the logarithmic derivative against the continued Gaussian
transform and the scale factor is literally the principal contour of the target.  This is a
naming step: no contour moves and no sum occurs. -/
theorem principal_half_line_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) = principalContour δ x := by
  sorry

/-! ### D. The line of real part minus one half is an admissible contour -/

/-- LEAF. The integrand of step three is integrable on the line of real part minus one
half: the continued Gaussian transform decays faster than any power in the height, the
logarithmic derivative grows only like the logarithm of the height, and the scale factor
has the constant modulus `x ^ (-1 / 2)`.  This is one integrability statement and nothing
else; it fixes no value of the integral, no residue and no zero sum, and it needs no
hypothesis on the zeros. -/
theorem principal_half_line_integrable (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  sorry

/-! ### E. The assembly -/

/-- The contour shift identity of the target, assembled from the three identities above by
rewriting and `ring` only.  The statement is the target's, unchanged; the assembly has no
sorry of its own and does not use the target theorem. -/
theorem principal_contour_shift_two_to_minus_half_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
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
  have h1 := principal_two_line_prime_sum x hx q χ δ
  have h2 := principal_half_line_conductor_one x hx q χ δ hq
  have h3 := principal_explicit_formula_shift x hx q χ δ T hq
  rw [h1, h3, h2]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_shift_two_to_minus_half_split
