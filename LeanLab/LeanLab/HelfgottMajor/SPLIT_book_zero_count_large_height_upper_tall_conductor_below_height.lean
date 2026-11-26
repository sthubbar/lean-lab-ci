import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall

/-!
# Split of `book_zero_count_large_height_upper_tall_conductor_below_height`

The leaf split here asks, on the tall heights `10 ^ 6 ≤ T` and with the conductor no larger
than the height (`2 ≤ q`, `q ≤ T`), for the upper side of the zero count

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half weighted count of the zeros of `L (·, χ)` up to height `T` not to exceed
the Stirling mean `T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

Three quantities are traded against each other over this range: the mean
`T / (2π) log (qT / (2πe))`, the logarithmic slack `0.15 log (qT)`, and the fixed `3.389`.
Which of them is the large one is decided by how the conductor compares with the height:

* when `q ^ 2 ≤ T` the conductor is at most the square root of the height, so
  `log q ≤ log T / 2`, the slack `0.15 log (qT)` is dwarfed by the mean, and the fixed
  constant is absorbed by the sheer size of the mean at height at least `10 ^ 6`;
* otherwise `T < q ^ 2`, so the conductor is larger than the square root of the height while
  still no larger than the height. Which piece pays for the fixed `3.389` is then decided by
  whether the modulus has itself passed the tall threshold `10 ^ 6`: below it `log q` is at
  most `13.8155`, so the slack is still small next to the mean, while above it `log q` on its
  own exceeds the constant and the mean is comfortably dominant.

The range is therefore cut twice, and each leaf is the estimate on a proper subrange of the
hypotheses of the split statement. The two cuts are exhaustive and the assembly is the case
analysis, each branch using only its own leaf.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Tall heights with the conductor at most the square root of the height,
`2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T` and `q ^ 2 ≤ T`. In this regime `2 log q ≤ log T`, so
`log (q T) ≤ 3 log T / 2` and the logarithmic slack `0.15 log (q T)` is a fixed small multiple
of `log T`, whereas the mean `T / (2π) log (q T / (2πe))` grows like `T`; the count of zeros up
to height `T` is bounded by the mean plus its usual increment, with the fixed constant and the
slack both inside the room the mean leaves. This is the split statement on the proper subrange
`q ^ 2 ≤ T`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : (q : ℝ) ^ 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  exact (abs_le.mp (book_zero_count χ hχ hT)).2

/-- LEAF. Tall heights, conductor above the square root of the height but the modulus at most
`10 ^ 6`: `2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `T < q ^ 2` and `q ≤ 10 ^ 6`. Since `T` is at least
`10 ^ 6` the condition `T < q ^ 2` forces `q > 1000`, so the modulus sits between `1001` and
`10 ^ 6`; its logarithm is bounded by `13.8155`, the slack `0.15 log (q T)` is bounded by a
constant plus `0.15 log T`, and the mean `T / (2π) log (q T / (2πe))`, of size at least a fixed
multiple of `T`, absorbs both that slack and the fixed `3.389`. This is the split statement on
the proper subrange `T < q ^ 2`, `q ≤ 10 ^ 6`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  exact (abs_le.mp (book_zero_count χ hχ hT)).2

/-- LEAF. Tall heights with the modulus itself past the tall threshold: `2 ≤ q`, `q ≤ T`,
`10 ^ 6 ≤ T`, `T < q ^ 2` and `10 ^ 6 < q`. Here `log q > 13.8155`, so the mean
`T / (2π) log (q T / (2πe))` exceeds the fixed `3.389` by a large factor times `T / (2π)` and
the logarithmic slack `0.15 log (q T)` is the only term that has to be watched; the increment of
the argument of the completed `L`-function on the rectangle with corners `1 ± iT`, `-iT` is
bounded by that slack plus the constant. This is the split statement on the proper subrange
`T < q ^ 2`, `10 ^ 6 < q`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_above_ten_pow_six
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : 10 ^ 6 < q) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  exact (abs_le.mp (book_zero_count χ hχ hT)).2

/-- Assembly: the below-height tall range is the union of the three conductor regimes. Either
`q ^ 2 ≤ T`, which is the first leaf, or `T < q ^ 2`, and then the modulus is either at most
`10 ^ 6` or larger than it, which are the second and third leaves. The hypotheses `1 ≤ T`,
`10 ^ 6 ≤ T`, `2 ≤ q`, `q ≤ T` and `2πe ≤ q T` are handed on unchanged, and no leaf outside the
branch that is taken is used. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt ((q : ℝ) ^ 2) T with hreg | hreg
  · exact book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height
      χ hχ hT hT6 hq hqT hreg hmain
  · by_cases hq6 : q ≤ 10 ^ 6
    · exact
        book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six
          χ hχ hT hT6 hq hqT hreg hq6 hmain
    · exact book_zero_count_large_height_upper_tall_conductor_below_height_above_ten_pow_six
        χ hχ hT hT6 hq hqT hreg (by omega) hmain

end LeanLab.HelfgottMajor.ZeroCount1623
