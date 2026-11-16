import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one`

The leaf split here is the level one case of the tall range: `q = 1`, `10 ^ 6 ≤ T`, and
`2 * π * exp 1 ≤ q * T`, asking for the upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half weighted zero count `bookCount χ T` not to exceed the Stirling mean
`T / (2π) log (T / (2π e))` by more than `0.15 log T + 3.389`.

At level one the conductor contributes `log 1 = 0` to `log (qT)`, so the error is the fixed
`3.389` plus `0.15 log T` and no conductor regime is left to cut: the height `T` alone has to
carry the argument, and the three scales below are where the two terms of the budget pull in
opposite directions.

* At the bottom of the tall range, `10 ^ 6 ≤ T ≤ 10 ^ 7`, the mean is already of size `10 ^ 6`
  and dwarfs `0.15 log T + 3.389`; the increment of the argument of the completed
  `L`-function on the rectangle with corners `1 ± iT`, `-iT` is compared with that mean, and
  the endpoint half weights at the heights `0` and `T` cost a fixed amount at a height which
  is itself bounded.
* In the middle, `10 ^ 7 ≤ T ≤ 10 ^ 13`, the Stirling remainder of the vertical line and the
  variation on the two horizontal segments each have to be kept below a fixed multiple of
  `log T`, which is the range in which a uniform remainder is needed rather than an asymptotic
  one.
* Above `10 ^ 13` the fixed `3.389` is negligible against the mean but the logarithmic charge
  is not, so all that has to hold is the uniform bound on the increment at every height past
  the cut.

Each leaf is the split statement on a closed subrange of the heights, and the assembly is the
case analysis on `T`; the hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `q = 1` and `2πe ≤ qT` are handed
on unchanged. The level one leaf is the case in which the conductor can never help, which is
why nothing but `T` is available to cut.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The error of the level one case, written out: at `q = 1` the conductor factor `q` is one,
so `bookError 1 T` is `0.15 log T` plus the fixed `3.389`. Used to compare the budget with the
mean at the two cuts. -/
private lemma bookError_one_eq (T : ℝ) :
    bookError 1 T = 0.15 * Real.log T + 3.389 := by
  simp [bookError]

/-- The mean of the level one case, written out: at `q = 1` the factor `q` is one, so
`bookMain 1 T` is `T / (2π)` times `log (T / (2πe))`. -/
private lemma bookMain_one_eq (T : ℝ) :
    bookMain 1 T = T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) := by
  simp [bookMain]

/-- The two cuts used by the case analysis are ordered and both sit above the tall threshold
`10 ^ 6`, so the three height scales cover the tall range and each of them is nonempty. -/
private lemma height_cuts : (10 : ℝ) ^ 6 ≤ 10 ^ 7 ∧ (10 : ℝ) ^ 7 ≤ 10 ^ 13 := by
  norm_num

/-- LEAF. Bottom of the tall range, `10 ^ 6 ≤ T ≤ 10 ^ 7`, at level one `q = 1`. The step is
the comparison of the increment of the argument of the completed `L`-function of `χ` on the
rectangle with corners `1 ± iT` and `-iT` with its mean: on the vertical line the increment is
the Stirling mean `T / (2π) log (T / (2π e))` up to a remainder of order `log T`, on the two
horizontal segments it is a half at each end height `0` and `T`, and both are inside
`0.15 log T + 3.389`, whose size on this range is fixed by `T ≤ 10 ^ 7` while the mean is a
fixed multiple of `T`. This is the split statement on the proper subrange `T ≤ 10 ^ 7`. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : T ≤ 10 ^ 7)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Middle of the tall range, `10 ^ 7 ≤ T ≤ 10 ^ 13`, at level one `q = 1`. The step is
the uniform estimate on the same rectangle at heights where the logarithmic charge is the
whole budget: the Stirling remainder on the vertical segment and the variation on the two
horizontal segments are each `O (log T)`, the endpoint half weights at `0` and `T` contribute
only through the multiplicities at those two heights, and the sum of the three stays below
`0.15 log T + 3.389`. This is the split statement on the proper subrange
`10 ^ 7 ≤ T ≤ 10 ^ 13`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : 10 ^ 7 ≤ T) (hT13 : T ≤ 10 ^ 13)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Top of the tall range, `10 ^ 13 ≤ T`, at level one `q = 1`. The step is the uniform
bound past the last cut: the fixed `3.389` is negligible against the mean, so the estimate
reduces to keeping the increment of the argument of the completed `L`-function on the
rectangle with corners `1 ± iT`, `-iT` inside `0.15 log T` at every height past `10 ^ 13`,
with the mean absorbing the endpoint weights and the horizontal variation. This is the split
statement on the proper subrange `10 ^ 13 ≤ T`. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT13 : 10 ^ 13 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the level one tall range is the union of the three height scales. Either
`T ≤ 10 ^ 7`, which is the first leaf, or `10 ^ 7 ≤ T`, and then either `T ≤ 10 ^ 13` or not,
which are the second and third leaves. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `q = 1` and
`2πe ≤ q T` are handed on unchanged, and neither the target nor any statement about levels
other than one is used. -/
theorem book_zero_count_large_height_upper_tall_level_one_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T (10 ^ 7) with hT7 | hT7
  · exact book_zero_count_large_height_upper_tall_level_one_near_threshold χ hχ hT hT6 hq1 hT7
      hmain
  · have hT7' : 10 ^ 7 ≤ T := hT7.le
    rcases le_or_gt T (10 ^ 13) with hT13 | hT13
    · exact book_zero_count_large_height_upper_tall_level_one_middle_scale χ hχ hT hT6 hq1 hT7'
        hT13 hmain
    · exact book_zero_count_large_height_upper_tall_level_one_far_scale χ hχ hT hT6 hq1 hT13.le
        hmain

end LeanLab.HelfgottMajor.ZeroCount1623
