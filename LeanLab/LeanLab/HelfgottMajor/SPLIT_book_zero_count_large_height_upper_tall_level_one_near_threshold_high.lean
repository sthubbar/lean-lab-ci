import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_near_threshold
import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_near_threshold_low

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_near_threshold_high`

Same input as the low part of the near range: the single cited leaf
`trudgian2014_count_near_cited`, Trudgian JNT 134 (2014) display (1.2) with the remainder
identity behind Corollary 1, valid up to `5.45 * 10 ^ 8`, which covers `T ≤ 10 ^ 7`. It lives
in the file `SPLIT_book_zero_count_large_height_upper_tall_level_one_near_threshold_low`. No new
sorry here.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Exact statement of `book_zero_count_large_height_upper_tall_level_one_near_threshold_high`,
proved from the cited leaf `trudgian2014_count_near_cited` through `near_upper_from_cited`. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_high_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hTlo : 5 * 10 ^ 6 ≤ T) (hT7 : T ≤ 10 ^ 7)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T :=
  near_upper_from_cited χ hq1 hT6 (by linarith)

end LeanLab.HelfgottMajor.ZeroCount1623
