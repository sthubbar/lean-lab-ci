import LeanLab.HelfgottMajor.SPLIT_leaf_band_zero_count_at_top_small_level

/-!
Split of `leaf_band_zero_count_at_top_large_level`.  It uses the same cited leaf
`leaf_bmor_zero_count`, Bennett, Martin, O'Bryant, Rechnitzer, Math. Comp. 90 (2021),
Theorem 1.1, page 1456, and the proved arithmetic `top_band_count_le_13`, which covers every
`2 ≤ q ≤ 23`.  At `q = 12` the cited bound is about `6.3`, at `q = 23` about `3.6`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The target `leaf_band_zero_count_at_top_large_level`, with exactly its statement, from the
cited leaf `leaf_bmor_zero_count` and proved arithmetic. -/
theorem leaf_band_zero_count_at_top_large_level_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq12 : 12 ≤ q) (hq23 : q ≤ 23) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 :=
  top_band_count_le_13 q χ hχ (by omega) hq23

end LeanLab.HelfgottMajor.Decomp388a
