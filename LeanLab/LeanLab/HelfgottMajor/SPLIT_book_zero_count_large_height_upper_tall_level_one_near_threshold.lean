import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_near_threshold`

The leaf split here is the bottom scale of the level one tall range: the modulus is one
(`q = 1`) and the height is `10 ^ 6 ≤ T ≤ 10 ^ 7`. What is asked is the upper side of the
zero count

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, that the half weighted count of the zeros of `L (·, χ)` with ordinate between `0`
and `T` does not exceed the Stirling mean `T / (2π) log (T / (2π e))` by more than
`0.15 log T + 3.389`.

At `q = 1` the conductor factor is one, so both `log (q T)` of the mean and `log (q T)` of the
error are `log T` and no conductor regime is left to cut: on this range the height alone has
to carry the argument. That is why the parent statement cuts on `T` alone, and why this one
cuts on `T` alone as well.

On this scale the two terms of the budget are of very different size. The mean is already
`T / (2π) log (T / (2π e))`, of size `T` at the bottom of the range and larger at the top,
while the error `0.15 log T + 3.389` is at most `0.15 log (10 ^ 7) + 3.389`, a fixed number:
the whole logarithmic charge is bounded on this scale, and what the estimate has to say is
that the increment of the argument of the completed `L`-function of `χ` on the rectangle with
corners `1 ± iT` and `-iT` — the Stirling remainder of the vertical segment plus the variation
on the two horizontal segments plus the half weights at the endpoint heights `0` and `T` —
stays below that mean plus a fixed number.

The range is therefore cut twice, at `2 * 10 ^ 6` and at `5 * 10 ^ 6`, and each leaf is the
split statement on a closed subrange of the heights, with the hypotheses `1 ≤ T`,
`10 ^ 6 ≤ T`, `q = 1` and `2 π e ≤ q T` handed on unchanged. The three subranges cover
`10 ^ 6 ≤ T ≤ 10 ^ 7` and the assembly is the case analysis; neither the target nor any
statement about another level or another scale is used.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The two cuts used by the case analysis lie inside the near range and above the tall
threshold `10 ^ 6`, so the three height subranges cover `10 ^ 6 ≤ T ≤ 10 ^ 7` and each of them
is nonempty. -/
private lemma near_cuts :
    (10 : ℝ) ^ 6 ≤ 2 * 10 ^ 6 ∧ 2 * 10 ^ 6 ≤ 5 * 10 ^ 6 ∧ 5 * 10 ^ 6 ≤ 10 ^ 7 := by
  norm_num

/-- LEAF. Bottom of the near range, `10 ^ 6 ≤ T ≤ 2 * 10 ^ 6`, at level one `q = 1`. The step
is the comparison of the increment of the argument of the completed `L`-function of `χ` on the
rectangle with corners `1 ± iT` and `-iT` with the mean at a height where the mean is of size
`T` and the budget `0.15 log T + 3.389` is bounded by `0.15 log (2 * 10 ^ 6) + 3.389`: the
Stirling remainder of the vertical segment and the variation on the two horizontal segments,
together with the half weights at the endpoint heights `0` and `T`, are kept below the mean
plus that fixed amount. This is the split statement on the proper subrange `T ≤ 2 * 10 ^ 6`. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_low
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hTup : T ≤ 2 * 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Middle of the near range, `2 * 10 ^ 6 ≤ T ≤ 5 * 10 ^ 6`, at level one `q = 1`. The
step is the same comparison one dyadic scale higher: the mean `T / (2π) log (T / (2π e))` has
grown by the factor `T` of the comparison, the fixed `3.389` and the endpoint half weights at
the heights `0` and `T` are unchanged, and `0.15 log T` is still at most
`0.15 log (5 * 10 ^ 6)`, so what has to hold is that the increment of the argument on the
rectangle with corners `1 ± iT` and `-iT` stays inside the mean plus that fixed number. This
is the split statement on the proper subrange `2 * 10 ^ 6 ≤ T ≤ 5 * 10 ^ 6`. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_middle
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hTlo : 2 * 10 ^ 6 ≤ T) (hTup : T ≤ 5 * 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Top of the near range, `5 * 10 ^ 6 ≤ T ≤ 10 ^ 7`, at level one `q = 1`. The step is
the comparison at the largest heights of this scale, where the mean is at least of size
`5 * 10 ^ 6` while the whole budget is at most `0.15 log (10 ^ 7) + 3.389`: the increment of
the argument of the completed `L`-function of `χ` on the rectangle with corners `1 ± iT` and
`-iT`, its vertical Stirling part and the variation on the two horizontal segments together,
stays below the mean, the endpoint half weights at `0` and `T` being absorbed by the same
margin. This is the split statement on the proper subrange `5 * 10 ^ 6 ≤ T ≤ 10 ^ 7`, the top
of the near range. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_high
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hTlo : 5 * 10 ^ 6 ≤ T) (hT7 : T ≤ 10 ^ 7)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the near range `10 ^ 6 ≤ T ≤ 10 ^ 7` is the union of the three height
subranges. Either `T ≤ 2 * 10 ^ 6`, which is the first leaf, or `2 * 10 ^ 6 ≤ T`, and then
either `T ≤ 5 * 10 ^ 6` or not, which are the second and third leaves. The hypotheses `1 ≤ T`,
`10 ^ 6 ≤ T`, `q = 1` and `2πe ≤ q T` are handed on unchanged, and neither the target nor any
statement about another level or another scale is used. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : T ≤ 10 ^ 7)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T (2 * 10 ^ 6) with hT20 | hT20
  · exact book_zero_count_large_height_upper_tall_level_one_near_threshold_low χ hχ hT hT6 hq1
      hT20 hmain
  · have hTlo : 2 * 10 ^ 6 ≤ T := hT20.le
    rcases le_or_gt T (5 * 10 ^ 6) with hT50 | hT50
    · exact book_zero_count_large_height_upper_tall_level_one_near_threshold_middle χ hχ hT hT6
        hq1 hTlo hT50 hmain
    · exact book_zero_count_large_height_upper_tall_level_one_near_threshold_high χ hχ hT hT6 hq1
        hT50.le hT7 hmain

end LeanLab.HelfgottMajor.ZeroCount1623
