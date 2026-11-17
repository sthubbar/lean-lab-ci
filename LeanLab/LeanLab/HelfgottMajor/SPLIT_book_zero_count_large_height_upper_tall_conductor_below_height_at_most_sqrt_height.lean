import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_conductor_below_height

/-!
# Split of `book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height`

The leaf asks, on the tall heights `10 ^ 6 ≤ T` with `2 ≤ q`, `q ≤ T` and `q ^ 2 ≤ T`, so that
the conductor is at most the square root of the height, for the upper side of the zero count

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half weighted count of the zeros of `L (·, χ)` up to height `T` not to exceed
the Stirling mean `T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

On this range the conductor is pinned between the two ends `2` and `T`: `q ^ 2 ≤ T` gives
`log q ≤ log T / 2`, hence `log (q T) ≤ 3 log T / 2`, and the only freedom the conductor keeps
is whether the modulus `q` has itself passed the tall threshold `10 ^ 6`. Below that threshold
`log q ≤ 13.8155`, so the logarithmic part of the error is a fixed multiple against a mean of
size at least of order `10 ^ 6`; above it the main term grows with `log q`, so the mean is even
more dominant and a single factor of `T / (2π)` pays the fixed `3.389`.

The range is therefore cut once, at `q = 10 ^ 6`, and each leaf is the estimate on a proper
subrange of the hypotheses of the split statement. The two cuts are exhaustive, the assembly is
the case analysis, and each branch uses only its own leaf.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Tall heights with the conductor at most the square root of the height and the modulus
itself no larger than `10 ^ 6`: `2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `q ^ 2 ≤ T` and `q ≤ 10 ^ 6`.
Here `log q ≤ 13.8155`, so `log (q T) ≤ log T + 13.8155` and the whole error
`0.15 log (q T) + 3.389` is at most `0.15 log T + 5.4618`, while the mean is at least
`T / (2π) log (T / (2πe))`, which at height `10 ^ 6` already exceeds that by a large factor; the
mean absorbs both the logarithmic slack and the fixed constant. This is the split statement on
the proper subrange `q ≤ 10 ^ 6`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height_below_ten_pow_six
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : (q : ℝ) ^ 2 ≤ T)
    (hq6 : q ≤ 10 ^ 6) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Tall heights with the modulus past the tall threshold while still at most the square
root of the height: `2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `q ^ 2 ≤ T` and `10 ^ 6 < q`. Here
`log q > 13.8155`, so `log (q T) > 13.8155 + log T` and the main term `T / (2π) log (q T / 2πe)`
exceeds the fixed `3.389` by a factor of order `T`, with the logarithmic slack `0.15 log (q T)`
the only term left to watch; since `q ^ 2 ≤ T` also gives `log q ≤ log T / 2`, that slack is at
most `0.45 log T`, which the mean covers with room. This is the split statement on the proper
subrange `10 ^ 6 < q`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height_above_ten_pow_six
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : (q : ℝ) ^ 2 ≤ T)
    (hq6 : 10 ^ 6 < q) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: on the tall range with the conductor at most the square root of the height, the
modulus is either at most `10 ^ 6`, which is the first leaf, or larger than it, which is the
second leaf. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `2 ≤ q`, `q ≤ T`, `q ^ 2 ≤ T` and
`2πe ≤ q T` are handed on unchanged, and no leaf outside the branch that is taken is used. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : (q : ℝ) ^ 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt q (10 ^ 6) with hq6 | hq6
  · exact
      book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height_below_ten_pow_six
        χ hχ hT hT6 hq hqT hreg hq6 hmain
  · exact
      book_zero_count_large_height_upper_tall_conductor_below_height_at_most_sqrt_height_above_ten_pow_six
        χ hχ hT hT6 hq hqT hreg hq6 hmain

end LeanLab.HelfgottMajor.ZeroCount1623
