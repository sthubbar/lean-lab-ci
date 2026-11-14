import LeanLab.HelfgottMajor.Decomp503a

/-!
Split of `saddle_pair_expansion` of `HelfgottMajor/Decomp503a.lean`.

The target bounds the sum of the two reflected Gaussian Mellin norms, at a nonzero
shift and at height at least `max 100 (4 * π ^ 2 * |δ|)`, by

`4.217 * exp (-E * |im|) + saddleRemainder δ im`,

where `E` is the saddle rate `BookE.E (|im| / (π * δ) ^ 2)` of display 3.68.  The
saddle expansion of Theorem 3.1 produces one term for `s` and one for `1 - s`, and the
constant `4.217` is the sum of the two coefficients: the k equal to zero coefficient
of display 3.69 is symmetric in the two reflections, and its two copies add to the
paper's `4.217`.  The cut below is exactly that split.  Each leaf bounds one of the
two Mellin norms by its own half of the constant and its own half of the remainder;
nothing in a leaf mentions the other reflection or the sum, so no leaf restates the
target, and the assembly is arithmetic only.

Degenerate values, checked before the cut was kept.  The shift hypothesis `δ ≠ 0` is
what makes `(π * δ) ^ 2` and `2 * π * |δ|` nonzero, so neither the saddle rate nor the
remainder divides by zero; at `δ = 0` the target would be a different (zero shift)
statement and is excluded by `hδ`, not by the cut.  The strip hypothesis allows
`s.re = 0` and `s.re = 1`; at `s.re = 0` the raw Mellin integral is not convergent and
`gaussianMellin δ s` is `0` in the integral convention, so the leaf holds there for
free, and at `s.re = 1` the reflected point has real part `0`, so the two leaves cover
the two boundaries.  The height hypothesis excludes small heights, so no leaf claims
anything at `s.im = 0`; it is satisfiable, for instance at `δ = 1` and `s = 1 / 2 + 100 i`,
where `max 100 (4 * π ^ 2) = 100 ≤ 100 = |s.im|`.  A negative `δ` and a negative
imaginary part change neither `(π * δ) ^ 2` nor `|s.im|`, so the leaves are invariant
under the reflection `δ ↦ -δ` and `s ↦ conj s` and the negative cases add nothing.
There is no empty set and no finite small case in either leaf: both are pointwise
statements about one complex number, and the whole difficulty sits in the saddle
expansion itself, which is what the leaves hand to the next worker.
-/

namespace LeanLab.HelfgottMajor.Decomp503a
open Real SplitGaussian123

/-- LEAF. The saddle expansion at the point `s` itself.  Theorem 3.1 continued to the
critical strip gives, for a single Mellin value at height `|s.im|` and shift `δ`, the
main exponential `exp (-E * |s.im|)` with the k equal to zero coefficient of display
3.69, plus the two explicit residual terms of displays 3.73 to 3.75, which together are
`saddleRemainder δ s.im`.  Here the coefficient is already cut down to `2.1085`, half of
the pair constant `4.217`, and the residual is cut down to `saddleRemainder δ s.im / 2`,
so this leaf is one side of the target and says nothing about `1 - s`.  It is strictly
easier than the target: the target bounds the sum of the two sides, this bounds one. -/
theorem leaf_saddle_expansion_at_s (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ ≤
      2.1085 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        saddleRemainder δ s.im / 2 := by
  sorry

/-- LEAF. The saddle expansion at the reflected point `1 - s`.  This is the same single
Mellin bound as the previous leaf, applied to `1 - s`, whose real part `1 - s.re` is again
in the closed critical strip and whose imaginary part is `-s.im`, so both `|(1 - s).im|`
and the saddle rate `BookE.E (|(1 - s).im| / (π * δ) ^ 2)` are the same numbers as at `s`
and the statement is written with `|s.im|` for that reason.  It carries the other half
`2.1085` of the constant and the other half `saddleRemainder δ s.im / 2` of the
remainder.  It is strictly easier than the target and independent of the previous leaf:
neither implies the other, and the target does not imply either. -/
theorem leaf_saddle_expansion_at_one_sub_s (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ (1 - s)‖ ≤
      2.1085 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        saddleRemainder δ s.im / 2 := by
  sorry

/-- The pair expansion of Corollary 3.2 at `k` equal to zero, assembled from the two
one-sided saddle expansions: the two halves of the coefficient add to the paper's
`4.217`, the two halves of the residual add to `saddleRemainder δ s.im`, and what is left
is the arithmetic of the sum. -/
theorem saddle_pair_expansion_split (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        saddleRemainder δ s.im := by
  have h1 := leaf_saddle_expansion_at_s δ s hδ hσ0 hσ1 hτ
  have h2 := leaf_saddle_expansion_at_one_sub_s δ s hδ hσ0 hσ1 hτ
  linarith only [h1, h2]

end LeanLab.HelfgottMajor.Decomp503a
