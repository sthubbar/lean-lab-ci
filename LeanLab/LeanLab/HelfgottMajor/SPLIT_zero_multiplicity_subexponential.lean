import LeanLab.HelfgottMajor.SPLIT_mass_pointwise_envelope

/-!
Splitting `Decomp269c.zero_multiplicity_subexponential` into five steps.

The target bounds the multiplicity of a zero of `L (s, χ)` in the open critical strip above
height `100` by `exp (0.6 * |im|)`. The right hand side carries no conductor, so the proof
has two ingredients: a multiplicity weighted zero count, which is where the conductor enters
and which is logarithmic in `q * T`, and the dominance of the exponential `exp (0.6 * t)`
over that logarithm at height at least `100`.

`ZeroCount1623.bookCount χ T` is the multiplicity weighted count of the zeros of `L (·, χ)`
in the open strip with imaginary part between `0` and `T`, one half at each of the two end
heights. A single zero at height `|im|` is therefore one of the counted zeros, at an interior
height, so its multiplicity is at most the count at height `|im| + 1`. That is the first two
leaves, one for each half of the plane: for a zero with nonnegative imaginary part the count
of `χ` sees it directly, and for a zero below the real axis the conjugation symmetry reflects
it to a zero of `χ⁻¹` above the real axis.

The count itself is bounded by the explicit Riemann–von Mangoldt main term plus its error,
which is the third leaf. The last two leaves are the arithmetic: the main term and the error
at height `t + 1` are each at most half of `exp (0.6 * t)` for `t` at least `100`, so their
sum fits under the single exponential of the target.

The assembly is the two cases of the sign of the imaginary part, the count, and the two halves
added. `zero_multiplicity_subexponential` itself is not used.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. A zero with nonnegative imaginary part is counted. The zero `s` lies in the open
strip by hypothesis, has imaginary part at least `100` and hence at most `|im| + 1`, and is an
interior height of the count, so its weight in `bookCount χ (|im| + 1)` is one and its
multiplicity is at most the whole multiplicity weighted count. The count is taken at
`|im| + 1` rather than at `|im|` precisely so that no factor of one half appears. -/
theorem order_le_book_count_upper (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : DirichletCharacter.LFunction χ s = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) (him0 : 0 ≤ s.im) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ) ≤
      ZeroCount1623.bookCount χ (|s.im| + 1) := by
  sorry

/-- LEAF. A zero with negative imaginary part is counted by the inverse character. The
conjugation symmetry of the `L`-function reflects `s` to `conj s`, a zero of `χ⁻¹` with
imaginary part `|im| ≥ 100` and the same multiplicity, so the previous leaf applies to the
inverse character at the reflected height. This is the second half of the plan, and no
analytic input is used. -/
theorem order_le_book_count_lower (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : DirichletCharacter.LFunction χ s = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) (himneg : s.im < 0) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ) ≤
      ZeroCount1623.bookCount χ⁻¹ (|s.im| + 1) := by
  sorry

/-- LEAF. The counting input: above height `100` the multiplicity weighted count of the zeros
of `L (·, χ)` is at most the explicit main term `bookMain` plus the explicit error
`bookError`. This is the one sided consequence of the two sided explicit Riemann–von
Mangoldt estimate, stated for an arbitrary character so that neither the principal character
nor an imprimitive character needs a separate reduction. Heights below `100` are excluded
because the main term changes sign at small heights. -/
theorem book_count_le_main_add_error (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T) :
    ZeroCount1623.bookCount χ T ≤ ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  sorry

/-- LEAF. The main term is exponentially small at height at least `100`. The main term is
`T / (2 * π)` times the logarithm of `q * T / (2 * π * e)`, which is linear in `T` up to a
logarithm, so at `T = t + 1` and `t` at least `100` it is far below the half of
`exp (0.6 * t)`. This is the first half of the exponential dominance and uses no zero of
`L (s, χ)`. -/
theorem book_main_le_half_exp (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    ZeroCount1623.bookMain q (t + 1) ≤ exp (0.6 * t) / 2 := by
  sorry

/-- LEAF. The error term is exponentially small at height at least `100`. The error
`0.15 * log (q * T) + 3.389` grows only like a logarithm, so at `T = t + 1` and `t` at least
`100` it is far below the half of `exp (0.6 * t)`. This is the second half of the exponential
dominance, and again no zero is involved. -/
theorem book_error_le_half_exp (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  sorry

/-- The target, assembled from the five steps. A zero of the open strip above height `100`
has nonnegative or negative imaginary part. In the first case the upper count sees it and in
the second the inverse character counts the reflection; in both cases the count at height
`|im| + 1` is at most the main term plus the error there, and the two halves of the
exponential add up to `exp (0.6 * |im|)`. -/
theorem zero_multiplicity_subexponential_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : DirichletCharacter.LFunction χ s = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ) ≤ exp (0.6 * |s.im|) := by
  have hhalf : exp (0.6 * |s.im|) / 2 + exp (0.6 * |s.im|) / 2 = exp (0.6 * |s.im|) := by
    ring
  have hmain := book_main_le_half_exp q |s.im| him
  have herr := book_error_le_half_exp q |s.im| him
  by_cases him0 : 0 ≤ s.im
  · have hcount := book_count_le_main_add_error q χ (|s.im| + 1) (by linarith)
    have horder := order_le_book_count_upper q χ s hs hre0 hre1 him him0
    linarith
  · have himneg : s.im < 0 := lt_of_not_ge him0
    have hcount := book_count_le_main_add_error q χ⁻¹ (|s.im| + 1) (by linarith)
    have horder := order_le_book_count_lower q χ s hs hre0 hre1 him himneg
    linarith
