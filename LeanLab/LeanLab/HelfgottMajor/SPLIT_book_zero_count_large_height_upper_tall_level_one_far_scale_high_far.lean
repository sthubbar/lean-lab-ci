import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_far_scale
import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_far_scale_low_far

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_far_scale_high_far`

Same input as the low part of the far range: the single cited leaf
`trudgian2014_corollary1_far_cited`, Corollary 1 of Trudgian JNT 134 (2014), valid for all
`T ≥ e`, lives in the file
`SPLIT_book_zero_count_large_height_upper_tall_level_one_far_scale_low_far`, which also holds
the proved level one bridge and the arithmetic for every `T ≥ 10 ^ 13`. No new sorry here.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Exact statement of `book_zero_count_large_height_upper_tall_level_one_far_scale_high_far`,
proved from the cited leaf `trudgian2014_corollary1_far_cited` through
`far_upper_from_cited`. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_high_far_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT100 : 10 ^ 100 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T :=
  far_upper_from_cited χ hq1 (le_trans (by norm_num) hT100)

end LeanLab.HelfgottMajor.ZeroCount1623
