import LeanLab.HelfgottMajor.SPLIT_book_zero_count

/-!
# Split of `book_zero_count_large_height_upper` (`HelfgottMajor/ZeroCount1623`)

The leaf asks, on the range `2 ≤ T` and `2πe ≤ qT`, for the upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half-weighted zero count `bookCount χ T` not to exceed the main term
`T/(2π) log (qT/(2πe))` by more than `0.15 log (qT) + 3.389`.

Unlike the lower side there is no side condition that settles anything here: the count is a
sum of nonnegative half-weighted multiplicities and the main term is nonnegative on this
range, so the upper side is the genuinely quantitative direction, and the height `T` decides
which counting argument is available.

At height `T ≤ 20` only the finitely many zeros of the one `L`-function of `χ` up to a small
height are seen, and the height factor `T/(2π) ≤ 3.2` of the main term keeps it below the
error budget while `q` grows; the count is then a multiplicity sum over a fixed stretch of
the strip, whose size is governed by `log q` alone.

Above that height the increment of the argument of the completed `L`-function around the
rectangle with corners `1 ± iT`, `-iT` is what carries the bound, and the two ranges are
separated where the gamma factor still grows fast, `T ≤ 10^6`, and above it, where the
Stirling main term of order `T log T` dominates every contribution of the boundary. The
three ranges are disjoint and cover `T ≥ 2`, and the assembly selects among them by cases
on `T`.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Short height inside the large-height range, `2 ≤ T ≤ 20` with `2πe ≤ qT`. The zeros
counted have `0 ≤ Im ρ ≤ 20`, a fixed stretch of the strip, so the count is a multiplicity sum
over a set whose size is governed by `log q` alone, weighted one half at the two end heights
`0` and `T`; the main term grows like `T/(2π) log q` with `T ≤ 20`, and the error
`0.15 log (qT) + 3.389` has to absorb the difference. Only `T ≥ 2` and `T ≤ 20` are used, so
this is the target on a proper closed subrange of the heights. -/
theorem book_zero_count_large_height_upper_short (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Middle heights, `20 ≤ T ≤ 10^6` with `2πe ≤ qT`. On this range the argument of the
completed `L`-function of `χ` turns through `T/π log (qT/(2π)) - T/π` on the vertical line,
and the two horizontal segments contribute a variation bounded by the Stirling remainder, so
the increment stays below its mean plus `0.15 log (qT) + 3.389`; the half-weighted count of
zeros below `T` is then at most the main term plus the error. The variation is what needs the
growth of the gamma factor at `T ≥ 20`, which is why the range starts there. -/
theorem book_zero_count_large_height_upper_mid (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T) (hT6 : T ≤ 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Tall heights, `10^6 ≤ T` with `2πe ≤ qT`. Here the Stirling main term
`T/(2π) log (qT/(2πe))` dominates every contribution of the boundary, since the variation
along the horizontal segments and along the line `Re s = 1` is `O (log (qT))` against a main
term of order `T log T`, so the count of zeros below `T` cannot exceed the main term by more
than `0.15 log (qT) + 3.389`. This is the target on the subrange of heights above `10^6`. -/
theorem book_zero_count_large_height_upper_tall (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT6 : 10 ^ 6 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the upper side follows from the three height leaves. The cases `T ≤ 20` and
`20 ≤ T ≤ 10^6` are the first two leaves, and above `10^6` the third one; the hypotheses
`1 ≤ T` and `2πe ≤ qT` are passed along unchanged, and the target is nowhere used. -/
theorem book_zero_count_large_height_upper_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T 20 with hshort | hmid
  · exact book_zero_count_large_height_upper_short χ hχ hT hT2 hshort hmain
  · have hT20 : 20 ≤ T := hmid.le
    rcases le_or_gt T (10 ^ 6) with hmidd | htall
    · exact book_zero_count_large_height_upper_mid χ hχ hT hT20 hmidd hmain
    · exact book_zero_count_large_height_upper_tall χ hχ hT htall.le hmain

#print axioms book_zero_count_large_height_upper_split

end LeanLab.HelfgottMajor.ZeroCount1623
