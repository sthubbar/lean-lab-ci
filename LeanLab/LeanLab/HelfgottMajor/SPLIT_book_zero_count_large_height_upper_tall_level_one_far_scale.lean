import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_far_scale`

The leaf split here is the top of the level one tall range: the modulus is one
(`q = 1`) and the height is past the last of the three cuts made in the file this one
imports, `10 ^ 13 ≤ T`. What is asked is the upper side of the zero count

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, that the half weighted count of the zeros of `L (·, χ)` with ordinate between `0`
and `T` does not exceed the Stirling mean `T / (2π) log (T / (2π e))` by more than
`0.15 log T + 3.389`.

At `q = 1` the conductor factor is one, so the exponent `log (q T)` of the mean and the
`log (q T)` of the error do not depend on any second parameter: the height alone carries the
argument, and there is no conductor regime left to cut, which is why the parent statement
cuts on `T` alone and why this one has to cut on `T` alone as well.

What the cut below is for is that only two of the three quantities in the estimate still
move at this end of the range:

* The fixed `3.389` is already negligible at the bottom of this range, where the mean is of
  size `T` and `T` is at least `10 ^ 13`; the work at the bottom of the far range is the
  logarithmic slack `0.15 log T`, which grows without bound but only logarithmically.
* Once the height has passed a much larger cut the logarithmic slack is negligible against
  the increment of the mean between `T` and `T + 1` itself, the increment of the argument of
  the completed `L`-function on the rectangle with corners `1 ± iT` and `-iT` being what the
  estimate is about in the first place, so past that cut the two sides of the estimate are
  separated by a gap of size `T log T` rather than by a logarithm.

The range is therefore cut twice, at `10 ^ 20` and at `10 ^ 100`, and each leaf is the split
statement on a closed subrange of the heights, with the hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`,
`q = 1`, `10 ^ 13 ≤ T` and `2 π e ≤ q T` handed on unchanged. The three subranges cover
`10 ^ 13 ≤ T` and the assembly is the case analysis; neither the target nor any statement
about another level is used.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Bottom of the far range, `10 ^ 13 ≤ T ≤ 10 ^ 20`, at level one `q = 1`. The step is
the comparison of the increment of the argument of the completed `L`-function of `χ` on the
rectangle with corners `1 ± iT` and `-iT` with the mean at a height where the fixed `3.389`
is already negligible: the mean is of size `T`, hence at least `10 ^ 13`, while the error
`0.15 log T + 3.389` is at most `0.15 log (10 ^ 20) + 3.389`, a fixed number, so the estimate
is reduced to keeping the increment, the Stirling remainder of the vertical segment and the
variation on the two horizontal segments together, below the mean plus that fixed number.
This is the split statement on the proper subrange `T ≤ 10 ^ 20`. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_low_far
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT13 : 10 ^ 13 ≤ T) (hT20 : T ≤ 10 ^ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Middle of the far range, `10 ^ 20 ≤ T ≤ 10 ^ 100`, at level one `q = 1`. The step is
the same comparison at heights where the logarithmic slack `0.15 log T` is still the term that
has to be kept under control, while the mean is now so large that the fixed `3.389` and the
endpoint half weights at the heights `0` and `T` contribute a vanishing fraction of it: the
increment of the argument of the completed `L`-function on the rectangle with corners
`1 ± iT` and `-iT`, split into its vertical Stirling part and the variation on the two
horizontal segments, is bounded by the mean plus `0.15 log T` at every height of this range.
This is the split statement on the proper subrange `10 ^ 20 ≤ T ≤ 10 ^ 100`. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_mid_far
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT20 : 10 ^ 20 ≤ T) (hT100 : T ≤ 10 ^ 100)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Top of the far range, `10 ^ 100 ≤ T`, at level one `q = 1`. The step is the uniform
bound past the last cut, where both the fixed `3.389` and the logarithmic slack `0.15 log T`
are negligible against the increment of the mean: the mean `T / (2π) log (T / (2π e))` grows
like `T log T`, so what has to hold here is only that the increment of the argument of the
completed `L`-function of `χ` on the rectangle with corners `1 ± iT` and `-iT` stays within
the mean plus `0.15 log T` for every height past `10 ^ 100`, with the endpoint half weights
and the horizontal variation absorbed by the mean. This is the split statement on the proper
subrange `10 ^ 100 ≤ T`. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_high_far
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT100 : 10 ^ 100 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the far range `10 ^ 13 ≤ T` is the union of the three height subranges. Either
`T ≤ 10 ^ 20`, which is the first leaf, or `10 ^ 20 ≤ T`, and then either `T ≤ 10 ^ 100` or
not, which are the second and third leaves. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `q = 1`,
`10 ^ 13 ≤ T` and `2πe ≤ q T` are handed on unchanged, and no leaf outside the branch that is
taken is used. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT13 : 10 ^ 13 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T (10 ^ 20) with hT20 | hT20
  · exact book_zero_count_large_height_upper_tall_level_one_far_scale_low_far χ hχ hT hT6 hq1
      hT13 hT20 hmain
  · have hT20' : 10 ^ 20 ≤ T := hT20.le
    rcases le_or_gt T (10 ^ 100) with hT100 | hT100
    · exact book_zero_count_large_height_upper_tall_level_one_far_scale_mid_far χ hχ hT hT6 hq1
        hT20' hT100 hmain
    · exact book_zero_count_large_height_upper_tall_level_one_far_scale_high_far χ hχ hT hT6 hq1
        hT100.le hmain

end LeanLab.HelfgottMajor.ZeroCount1623
