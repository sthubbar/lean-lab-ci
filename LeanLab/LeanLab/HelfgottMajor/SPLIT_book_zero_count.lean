import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of `book_zero_count` (`HelfgottMajor/ZeroCount1623`)

`book_zero_count` bounds the book count `bookCount χ T` of a primitive `χ` mod `q` against
the main term `bookMain q T = T / (2π) * log (qT / (2πe))` and the error
`bookError q T = 0.15 * log (qT) + 3.389`, on the range `T ≥ 1`. The count is the sum over
the zeros of `L(·,χ)` in the open strip with `0 ≤ Im ρ ≤ T`, with multiplicity, and with
weight one half at the two end heights `0` and `T`.

The estimate is cut into four leaves. The first cut is by the size of the product `q * T`,
which is the quantity the main term depends on:

* `book_zero_count_band`, `q * T ≤ 2πe`. Here `log (qT / (2πe)) ≤ 0`, so the main term is
  nonpositive, and both `q` and `T` are bounded by `2πe ≤ 17.09`. Only the finitely many
  zeros below a fixed height of finitely many `L`-functions are counted, their total
  multiplicity is a small absolute constant, and the constant `3.389` of the error alone
  carries the inequality with room to spare. Nothing analytic is used.
* `book_zero_count_small_height`, `2πe ≤ q * T` and `T ≤ 2`. The height is at most `2`, so
  the count is still a bounded number of zeros of one fixed `L`-function, but `q` may now be
  large and the main term grows like `T / (2π) * log q`. The two sides grow at the same
  rate, and the difference is `O (log q)`, which is what the error `0.15 log (qT) + 3.389`
  of this range is meant to absorb; the zeros with `0 ≤ Im ρ ≤ 2` are the only ones it sees.
* `book_zero_count_large_height_upper` and `book_zero_count_large_height_lower`,
  `2 ≤ T` and `2πe ≤ q * T`. This range carries the asymptotic content, and it is the only
  range cut by the direction of the inequality, because there the two directions come from
  two different estimates of the increment of the argument of the completed `L`-function
  around the rectangle with corners `1 ± iT`, `-iT`: the upper side is a bound on how much
  that increment can exceed its Stirling mean, the lower side a bound on how far it can fall
  below it. On the two bounded ranges above, by contrast, both directions are the one
  crude finite-count argument, so cutting them apart would only duplicate that argument.

The three ranges are disjoint and exhaust `T ≥ 1`, and `book_zero_count_split` selects
among them: `abs_le` on the large-height range, and the two bounded-range leaves give the
whole absolute value statement at once.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Bounded band, `q * T ≤ 2πe`. The band bounds the conductor and the height at once,
`q ≤ 2πe` and `T ≤ 2πe`, since `q ≥ 1` and `T ≥ 1`; only zeros of `L(·,χ)` below the fixed
height `2πe` and inside the open unit strip are counted, so the count is a bounded absolute
constant with a bounded multiplicity. The main term is nonpositive here because
`log (qT / (2πe)) ≤ 0`, so the left side is the count plus the modulus of the main term, at
most `T / (2π) * log (2πe / (qT))`, which is at most `2πe / (2π) * log (2πe) < 4.8`; the
error is at least `3.389`. This is the first range of the cut, and it asserts nothing about
the analytic behaviour of `L`. -/
theorem book_zero_count_band (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  sorry

/-- LEAF. Small height, `2πe ≤ q * T` and `T ≤ 2`. The zeros counted lie with `0 ≤ Im ρ ≤ 2`,
a bounded stretch of the critical strip for the single `L`-function attached to `χ`, so what
is counted is a multiplicity sum over a set that does not grow with `q` (the zeros of an
`L`-function below a fixed height grow only like `log q`, and the height `2` leaves room for
the constant `3.389`). Both sides grow like `T / (2π) * log q`, and the difference is
carried by `0.15 * log (qT)`. This is the second range of the cut: the main term is already
nonnegative here, but the Stirling main term of the gamma factor is not yet available with a
sign, so the range is separated from the large-height one. -/
theorem book_zero_count_small_height (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  sorry

/-- LEAF. Large height, upper side. For `2 ≤ T` and `2πe ≤ q * T`, the increment of the
argument of the completed `L`-function of `χ` around the rectangle with corners `1 + iT`,
`-iT` is bounded above by its Stirling mean `T / π * log (qT / (2π)) - T / π` plus the
variation on the two horizontal segments and the vertical line, which is at most
`0.15 * log (qT) + 3.389` on this range; halving gives the upper bound for the half-weighted
upper count. The upper direction only needs the bound from above on that increment, so this
leaf is strictly weaker than the two sided statement. -/
theorem book_zero_count_large_height_upper (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Large height, lower side. On the same range `2 ≤ T`, `2πe ≤ q * T`, the same
increment of the argument is bounded below by its Stirling mean minus the variation along
the boundary, so the half-weighted upper count cannot fall below the main term by more than
the error `0.15 * log (qT) + 3.389`. This is the direction in which the count could a priori
be too small — a zero could sit exactly at a height at which the half weight of the book
count halves its contribution — and it needs the lower bound on the increment, which is a
different input from the upper bound used by the previous leaf. -/
theorem book_zero_count_large_height_lower (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  sorry

/-- Assembly: the split statement follows from the four leaves, with no appeal to the
target. Either `q * T ≤ 2πe`, which is the band leaf, or `2πe ≤ q * T` and then either
`T ≤ 2`, which is the small height leaf, or `2 ≤ T`, where the two one-sided leaves give the
two halves of `abs_le`. -/
theorem book_zero_count_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  by_cases hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1
  · exact book_zero_count_band χ hχ hT hband
  · have hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T := (not_le.mp hband).le
    by_cases hT2 : T ≤ 2
    · exact book_zero_count_small_height χ hχ hT hT2 hmain
    · have hT2' : 2 ≤ T := (not_le.mp hT2).le
      refine abs_le.mpr ⟨?_, book_zero_count_large_height_upper χ hχ hT hT2' hmain⟩
      linarith [book_zero_count_large_height_lower χ hχ hT hT2' hmain]

#print axioms book_zero_count_split

end LeanLab.HelfgottMajor.ZeroCount1623
