import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall

/-!
# Split of `book_zero_count_large_height_upper_tall_conductor_above_height`
(`HelfgottMajor/SPLIT_book_zero_count_large_height_upper_tall`)

The parent leaf asks, for `2 ≤ q` and `T ≤ q` on the tall heights `10 ^ 6 ≤ T` under
`2 * π * exp 1 ≤ q * T`, for

`bookCount χ T - bookMain q T ≤ bookError q T`,

with `bookMain q T = T / (2π) log (q T / (2π e))` and `bookError q T = 0.15 log (q T) + 3.389`.
On this range the conductor is at least the height, so `log (q T) ≥ log (T ^ 2)` and `log q` is
at least `log T`; the conductor is the parameter that can be large.

The estimate is sharp in its main term: the budget `bookError q T` is a few parts in `10 ^ 6` of
`bookMain q T` for every admissible pair, because `T ≥ 10 ^ 6` forces
`T / (2π) ≥ 1.5 · 10 ^ 5` while `0.15 log (q T)` grows only like the logarithm of the conductor.
So no leaf can lose a constant factor of the main term and still imply the target, and the only
cut available is the range. Each leaf below is therefore the parent statement on a proper
subrange, and the four subranges are the grid of two questions:

* is the conductor at most the square of the height, `q ≤ T ^ 2`, so that `log q ≤ 2 log T` and
  the whole budget is bounded by a multiple of `log T`; or is it beyond it, `T ^ 2 ≤ q`, so that
  `log q` is the dominant parameter and the main term grows with it;
* is the height in the bottom of the tall range, `T ≤ 10 ^ 7`, where the fixed constant `3.389`
  is the same order of magnitude as the logarithmic part `0.15 log (q T)` of the budget (at
  `T = 10 ^ 6` and `q = T ^ 2` they are `3.389` and `6.2`), or above it, where the constant is
  a small share of the budget and a proof may spend the logarithm freely.

The analytic input is common to all four and is not cut by this split: the bound on the increment
of the argument of the completed `L`-function of `χ` on the rectangle with corners `1`, `1 + iT`,
`iT` and `0`, whose Stirling mean is `bookMain q T` and whose variation along the boundary is what
`bookError q T` has to absorb. This is a partition of the conductor-above-height range, not a
decomposition of the estimate, and it is so on purpose: the estimate is sharp, so a leaf that
weakened it would not imply the target.

The assembly is the corresponding four way case split and uses each leaf once.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]


/-- LEAF. Conducting step for the conductor above the height but at most its square, in the
bottom of the tall range: `2 ≤ q`, `T ≤ q`, `q ≤ T ^ 2`, `10 ^ 6 ≤ T ≤ 10 ^ 7`, under
`2 * π * exp 1 ≤ q * T`. Here `log q ≤ 2 log T ≤ 32.2`, so the whole budget
`0.15 log (q T) + 3.389` is at most `7.3 + 3.389`, while the Stirling mean
`T / (2π) log (q T / (2π e))` is at least `1.5 · 10 ^ 5 · 24.8`; the argument increment of the
completed `L`-function on the rectangle `1`, `1 + iT`, `iT`, `0` has to stay below that mean plus
the budget with the fixed additive constant kept intact, which is the part of the estimate this
leaf carries. It is the parent statement on the proper subrange `q ≤ T ^ 2` of the bottom decade
of the tall range. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_below_squared_short
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hT7 : T ≤ 10 ^ 7) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hqs : (q : ℝ) ≤ T ^ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conducting step for a conductor beyond the square of the height, in the bottom of the
tall range: `2 ≤ q`, `T ^ 2 ≤ q`, `10 ^ 6 ≤ T ≤ 10 ^ 7`, under `2 * π * exp 1 ≤ q * T`. Now
`log q ≥ 2 log T ≥ 27.6` is the largest parameter, so the budget `0.15 log (q T) + 3.389` grows
with `log q` at the rate `0.15` while the Stirling mean `T / (2π) log (q T / (2π e))` grows with
`log q` at the rate `T / (2π) ≥ 1.5 · 10 ^ 5`: the ratio of the two is below `3 · 10 ^ (-6)`, and
the argument increment on the rectangle `1`, `1 + iT`, `iT`, `0` has to stay below its mean plus
the budget. Because the mean grows in the conductor, a variation bound of the form
`0.23 log q + 3.4` suffices, which is what the fixed constant has to cover here. This is the parent
statement on the proper subrange `T ^ 2 ≤ q` of the bottom decade of the tall range. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_beyond_squared_short
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hT7 : T ≤ 10 ^ 7) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hqs : T ^ 2 ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conducting step for the conductor above the height but at most its square, above the
bottom of the tall range: `2 ≤ q`, `T ≤ q`, `q ≤ T ^ 2`, `10 ^ 7 ≤ T`, under
`2 * π * exp 1 ≤ q * T`. Here `log (q T) ≤ 3 log T` and the budget
`0.15 log (q T) + 3.389 ≤ 0.45 log T + 3.4` is a small share of itself, while the Stirling mean
`T / (2π) log (q T / (2π e))` is at least `1.6 · 10 ^ 6 · 29.4`: the mean dominates the budget by
more than six orders of magnitude, and the argument increment on the rectangle `1`, `1 + iT`,
`iT`, `0` has to stay below the mean plus the budget, with the logarithm in the budget carrying
the room instead of the fixed constant. This is the parent statement on the proper subrange
`q ≤ T ^ 2` of the heights above `10 ^ 7`. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_below_squared_tall
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT7 : 10 ^ 7 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hqs : (q : ℝ) ≤ T ^ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conducting step for a conductor beyond the square of the height, above the bottom of
the tall range: `2 ≤ q`, `T ^ 2 ≤ q`, `10 ^ 7 ≤ T`, under `2 * π * exp 1 ≤ q * T`. Both
parameters are now large: `log q ≥ 32.2` and `T / (2π) ≥ 1.6 · 10 ^ 6`, so the Stirling mean
`T / (2π) log (q T / (2π e))` is at least `4.6 · 10 ^ 7` while the budget
`0.15 log (q T) + 3.389 ≤ 0.23 log q + 3.4` is a share below `3 · 10 ^ (-6)` of it; the argument
increment on the rectangle `1`, `1 + iT`, `iT`, `0` has to stay below the mean plus the budget,
and here both the region of integration and the budget may be handled coarsely in absolute terms
because the mean's growth in `log q` pays for everything. This is the parent statement on the
proper subrange `T ^ 2 ≤ q` of the heights above `10 ^ 7`. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_beyond_squared_tall
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT7 : 10 ^ 7 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hqs : T ^ 2 ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the conductor-above-height range follows from the four range leaves. Either the
height is at most `10 ^ 7`, and the bottom pair applies, or it is above it, and the tall pair
does; in each case either the conductor is at most `T ^ 2`, or beyond it, and the square is a
total order so one of the two always holds. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `2 ≤ q`,
`T ≤ q` and `2πe ≤ qT` are passed along unchanged, and the parent leaf is nowhere used. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T (10 ^ 7) with hT7 | hT7
  · rcases le_or_gt (q : ℝ) (T ^ 2) with hqs | hqs
    · exact book_zero_count_large_height_upper_tall_conductor_above_height_below_squared_short
        χ hχ hT hT6 hT7 hq hTq hqs hmain
    · exact book_zero_count_large_height_upper_tall_conductor_above_height_beyond_squared_short
        χ hχ hT hT6 hT7 hq hTq hqs.le hmain
  · rcases le_or_gt (q : ℝ) (T ^ 2) with hqs | hqs
    · exact book_zero_count_large_height_upper_tall_conductor_above_height_below_squared_tall
        χ hχ hT hT7.le hq hTq hqs hmain
    · exact book_zero_count_large_height_upper_tall_conductor_above_height_beyond_squared_tall
        χ hχ hT hT7.le hq hTq hqs.le hmain

end LeanLab.HelfgottMajor.ZeroCount1623
