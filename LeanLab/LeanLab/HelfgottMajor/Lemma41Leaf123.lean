import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p6, built on p5.
P0014 Helfgott, Major arcs for Goldbach's problem, Lemma 4.1, page 31, displays 4.1 to 4.3, for
the Gaussian weight as used on page 44, in CORRECTED form. This file holds that one LEAF.

The lab leaf SplitGaussian123.lemma_4_1_gaussian states the printed Lemma 4.1. It is SUSPECTED
FALSE for an even primitive character χ with q above 1: there L(0, χ) = 0, so L'/L has a simple
pole at s = 0 with residue 1, the Mellin transform G_δ has a simple pole there with residue
η(0), the pole of the product is double, and the factor x^s = 1 + s log x + ... adds
η(0) log x to the residue. Display 4.7 on page 33 defines R without the factor x^s and loses
that term. Candidate counterexample, reproduced by independent agents on 2026-11-12 and
2026-11-15: q = 5, the Legendre character, δ = 0, x = 20, where the printed inequality needs
an error of norm 1.916 against the allowed c0 = 1.40557, and the gap grows like log x.
Also the functional equation, display 4.8, relates L(s, χ) to L(1 − s, χ bar), so the constant
term carries L'/L(1, χ bar), the complex conjugate of L'/L(1, χ); display 4.2 prints χ.

The printed leaf is not changed. The corrected statement is written out with no definition:
the main part of the residue and the log x term appear in full.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Lemma41Leaf123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

open Classical in
/-- LEAF: P0014 Lemma 4.1, page 31, displays 4.1 to 4.3, for the Gaussian as used on page 44,
in CORRECTED form. R is the main part, log 2π for q equal to 1 and log(2π/q) + γ minus the
complex conjugate of L'(1, χ)/L(1, χ) else, plus log x when χ is even and q is above 1, plus an
error of norm at most c0 of display 4.3. Changes against the print: the log x of the double
pole at s = 0 that display 4.7 loses, and the conjugate, from display 4.8. As printed: the
norms of display 4.42 and the contour error (log q + 6.01)(|η'|₂ + 2π abs δ |η|₂) x^(-1/2),
with the true norms of record F-5032. -/
theorem lemma_4_1_gaussian_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    ∃ c : ℂ, ‖c‖ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T +
        ((if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
            ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
              (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
                DirichletCharacter.LFunction χ 1)) +
          (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0) + c)‖ ≤
        (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) / sqrt x := by
  sorry

end LeanLab.HelfgottMajor.Lemma41Leaf123
