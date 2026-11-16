import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_middle_scale`
(`HelfgottMajor/SPLIT_book_zero_count_large_height_upper_tall_level_one`)

The leaf is the middle height scale of the level one case of the tall range: `q = 1`,
`10 ^ 7 ≤ T ≤ 10 ^ 13`, and the upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, the half weighted zero count of the one `L`-function of the principal character not
exceeding `T / (2π) log (T / (2π e))` by more than `0.15 log T + 3.389`.

At level one the conductor contributes `log 1 = 0`, so the error `0.15 log (qT) + 3.389`
becomes the fixed `3.389` plus `0.15 log T`: the whole budget is a logarithm in the height.
Two mechanisms spend it on this scale and they cross over inside it. On the lower part of the
scale the Stirling mean `T / (2π) log (T / (2π e))` is still comparable to the height and the
logarithmic charge is a small multiple of `log T` against it, so the fixed `3.389` is the part
of the budget that pays for the variation of the argument on the two horizontal segments of
the rectangle with corners `1 ± iT` and `-iT`; on the upper part the mean has grown faster than
the error and what matters is that the Stirling remainder of the vertical segment and the
variation of the argument on the two horizontal segments be uniform, jointly below
`0.15 log T + 3.389`, at every height of the scale rather than only asymptotically.

This is a partition of the middle scale by the height, at the three cuts `10 ^ 8`, `10 ^ 10`
and `10 ^ 12`, not a decomposition of the estimate: each leaf is the target statement on a
proper closed subrange of its hypotheses, so each leaf is strictly easier than the target in
that the height is confined to a compact interval on which one of the two mechanisms above
decides the argument. The analytic input, the bound on the increment of the argument of the
completed `L`-function on the rectangle, is the same in all four, which is why no leaf is
weaker than the target in content, only in range. The assembly is the case analysis on `T`,
and the hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `q = 1`, `10 ^ 7 ≤ T`, `T ≤ 10 ^ 13` and
`2πe ≤ qT` are handed on unchanged.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The three cuts of the middle scale are ordered and all of them lie inside it, so the four
subranges of the partition are nonempty and cover `10 ^ 7 ≤ T ≤ 10 ^ 13`. -/
private lemma middle_scale_cuts :
    (10 : ℝ) ^ 7 ≤ 10 ^ 8 ∧ (10 : ℝ) ^ 8 ≤ 10 ^ 10 ∧
      (10 : ℝ) ^ 10 ≤ 10 ^ 12 ∧ (10 : ℝ) ^ 12 ≤ 10 ^ 13 := by
  norm_num

/-- LEAF. Bottom of the middle scale, `10 ^ 7 ≤ T ≤ 10 ^ 8`, at level one `q = 1`. The step is
the fixed `3.389` absorbing the variation of the argument of the completed `L`-function of `χ`
on the two horizontal segments of the rectangle with corners `1 ± iT` and `-iT`, while the
Stirling mean `T / (2π) log (T / (2π e))`, which at these heights is already a fixed multiple
of `T`, carries the vertical segment and the logarithmic charge `0.15 log T`; on a compact
height interval the three pieces are compared with `0.15 log T + 3.389` directly rather than
asymptotically. This is the target on the proper subrange `10 ^ 7 ≤ T ≤ 10 ^ 8`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_low
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : 10 ^ 7 ≤ T) (hT8 : T ≤ 10 ^ 8)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Lower central part of the middle scale, `10 ^ 8 ≤ T ≤ 10 ^ 10`, at level one
`q = 1`. The step is the crossover: here the logarithmic charge `0.15 log T` and the fixed
`3.389` are of the same size, so the Stirling remainder of the vertical segment has to be kept
below its mean value by a margin comparable to the whole budget, and the multiplicities at the
two end heights `0` and `T`, which the half weights of `bookCount` see, are absorbed only
through the fixed constant. This is the target on the proper subrange `10 ^ 8 ≤ T ≤ 10 ^ 10`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_central_low
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT8 : 10 ^ 8 ≤ T) (hT10 : T ≤ 10 ^ 10)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Upper central part of the middle scale, `10 ^ 10 ≤ T ≤ 10 ^ 12`, at level one
`q = 1`. The step is the uniform estimate in the range where the constant is negligible
against `0.15 log T`: the Stirling remainder on the vertical segment and the variation of the
argument on the two horizontal segments must each be `O (log T)` with the sum of the three
pieces below `0.15 log T + 3.389`, uniformly in `T` rather than in an asymptotic form. This is
the target on the proper subrange `10 ^ 10 ≤ T ≤ 10 ^ 12`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_central_high
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT10 : 10 ^ 10 ≤ T) (hT12 : T ≤ 10 ^ 12)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Top of the middle scale, `10 ^ 12 ≤ T ≤ 10 ^ 13`, at level one `q = 1`. The step is
the last uniformly bounded stretch before the far scale takes over: the mean
`T / (2π) log (T / (2π e))` has outgrown the budget by many orders, so the estimate reduces to
the increment of the argument of the completed `L`-function on the rectangle with corners
`1 ± iT`, `-iT` staying inside `0.15 log T` up to the last cut, with the mean absorbing both
endpoint half weights and the horizontal variation. This is the target on the proper subrange
`10 ^ 12 ≤ T ≤ 10 ^ 13`. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_top
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT12 : 10 ^ 12 ≤ T) (hT13 : T ≤ 10 ^ 13)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the middle scale follows from the four height subranges. Either `T ≤ 10 ^ 8`,
which is the low leaf, or `10 ^ 8 ≤ T`, and then either `T ≤ 10 ^ 10`, `T ≤ 10 ^ 12`, or
neither, which are the other three leaves at the cuts of `middle_scale_cuts`. The hypotheses
`1 ≤ T`, `10 ^ 6 ≤ T`, `q = 1`, `10 ^ 7 ≤ T`, `T ≤ 10 ^ 13` and `2πe ≤ qT` are passed along
unchanged, and neither the target statement nor any statement about another height scale or
another conductor is used. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : 10 ^ 7 ≤ T) (hT13 : T ≤ 10 ^ 13)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt T ((10 : ℝ) ^ 8) with h8 | h8
  · exact book_zero_count_large_height_upper_tall_level_one_middle_scale_low χ hχ hT hT6 hq1
      hT7 h8 hmain
  · have h8' : (10 : ℝ) ^ 8 ≤ T := h8.le
    rcases le_or_gt T ((10 : ℝ) ^ 10) with h10 | h10
    · exact book_zero_count_large_height_upper_tall_level_one_middle_scale_central_low χ hχ hT
        hT6 hq1 h8' h10 hmain
    · have h10' : (10 : ℝ) ^ 10 ≤ T := h10.le
      rcases le_or_gt T ((10 : ℝ) ^ 12) with h12 | h12
      · exact book_zero_count_large_height_upper_tall_level_one_middle_scale_central_high χ hχ
          hT hT6 hq1 h10' h12 hmain
      · exact book_zero_count_large_height_upper_tall_level_one_middle_scale_top χ hχ hT hT6
          hq1 h12.le hT13 hmain

#print axioms book_zero_count_large_height_upper_tall_level_one_middle_scale_split

end LeanLab.HelfgottMajor.ZeroCount1623
