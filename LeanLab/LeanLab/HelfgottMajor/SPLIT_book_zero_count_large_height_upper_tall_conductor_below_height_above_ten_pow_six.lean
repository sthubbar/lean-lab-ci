import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_conductor_below_height

/-!
# Split of `book_zero_count_large_height_upper_tall_conductor_below_height_above_ten_pow_six`

The leaf asks, on tall heights `10 ^ 6 ≤ T`, for a primitive character of modulus `2 ≤ q ≤ T`
whose conductor is above the square root of the height, `T < q ^ 2`, and which has itself passed
the tall threshold, `10 ^ 6 < q`, for the upper side of the zero count

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half weighted count of the zeros of `L (·, χ)` up to height `T` not to exceed
the Stirling mean `T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

Two parameters are left free on this range, and the way the error budget is spent depends on
which of them is large:

* the logarithmic slack `0.15 log (qT)` grows with `log q`, and since the modulus is above
  `10 ^ 6` that slack already has size `0.15 * 13.8155 = 2.0722` at the bottom of the range,
  rising by `0.15` for every factor `e` of `q`;
* the fixed `3.389` is paid out of the mean `T / (2π) log (qT / (2πe))`, whose growth in `T` is
  what makes it available.

The two cross at `log q = 3.389 / 0.15 = 22.5933`, that is at `q = exp 22.5933 = 6.49 * 10 ^ 9`:
below the crossing the constant is the larger of the two absolute terms and the mean has to
carry it, above the crossing the slack alone already exceeds it and the mean is only needed to
cover the slack and the arithmetic.

The range is therefore cut once, at `10 ^ 10`, a round modulus just above the crossing (there
`0.15 * log 10 ^ 10 = 0.15 * 23.0259 = 3.4539 > 3.389`), and each leaf is the estimate on a
proper subrange of the hypotheses of the split statement. The two cuts are exhaustive, the
assembly is the case analysis, and each branch uses only its own leaf.

The upper side is of course also what the two sided book count at height `T` gives, since
`a ≤ |a|`; what the cut adds is the location of each of the two absolute terms in the budget,
which is what a supporter of this range has to bound.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: tall heights, conductor above the square root of the height, modulus past `10 ^ 6` and
at most `10 ^ 10`: `2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `T < q ^ 2`, `10 ^ 6 < q`, `q ≤ 10 ^ 10`.
Here `log q ≤ 23.0259`, so `log (q T) ≤ log T + 23.0259` and the whole error
`0.15 log (q T) + 3.389` is at most `0.15 log T + 6.8429`, while the mean is at least
`T / (2π) log (T / (2πe))`; the increment of the argument of the completed `L`-function over the
rectangle with corners `1 ± iT`, `-iT` has to stay inside that room. This is the parent
statement on the subrange `q ≤ 10 ^ 10`, the side of the crossing `log q = 3.389 / 0.15` where
the constant is the larger absolute term. -/
theorem book_zero_count_large_height_upper_tall_above_ten_pow_six_below_ten_pow_ten
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : 10 ^ 6 < q) (hq10 : q ≤ 10 ^ 10)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF: tall heights, conductor above the height's square root and modulus past `10 ^ 10`:
`2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `T < q ^ 2`, `10 ^ 10 < q`. Here `q > 10 ^ 10` gives
`0.15 log (q T) > 3.4539 + 0.15 log T`, so the slack alone already exceeds the fixed `3.389` and
the error sits inside the first order term `0.15 log (q T)`; `q ≤ T` gives `log (q T) ≤ 2 log T`
and the mean `T / (2π) log (q T / (2πe))` grows like `T log q / (2π)`, so the increment of the
argument of the completed `L`-function on the rectangle with corners `1 ± iT`, `-iT` stays inside
it. This is the parent statement on the subrange `10 ^ 10 < q`, the side of the crossing where
the slack is the larger term. -/
theorem book_zero_count_large_height_upper_tall_above_ten_pow_six_above_ten_pow_ten
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : 10 ^ 6 < q) (hq10 : 10 ^ 10 < q)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: on the tall range with the conductor above the square root of the height and past
`10 ^ 6`, either `q ≤ 10 ^ 10`, which is the first leaf, or `10 ^ 10 < q`, which is the second.
The hypotheses are handed on unchanged and no leaf outside the branch taken is used. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_above_ten_pow_six_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : 10 ^ 6 < q) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt q (10 ^ 10) with hq10 | hq10
  · exact book_zero_count_large_height_upper_tall_above_ten_pow_six_below_ten_pow_ten
      χ hχ hT hT6 hq hqT hreg hq6 hq10 hmain
  · exact book_zero_count_large_height_upper_tall_above_ten_pow_six_above_ten_pow_ten
      χ hχ hT hT6 hq hqT hreg hq6 hq10 hmain

#print axioms book_zero_count_large_height_upper_tall_conductor_below_height_above_ten_pow_six_split

end LeanLab.HelfgottMajor.ZeroCount1623
