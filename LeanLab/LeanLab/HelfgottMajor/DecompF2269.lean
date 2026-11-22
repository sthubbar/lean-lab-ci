import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_far_scale

/-!
# Split of the high far level one zero count estimate

FREE-nv-step task2269. This file imports the target module and does not edit it.
The target is the upper side of the zero count estimate at level one and height at least
`10 ^ 100`. The proof has three steps. First the height cut gives the lower height bound
required by the shared two sided estimate. Second the shared estimate gives the absolute
error between the weighted zero count and the main term. Third the upper half of that
absolute estimate gives the requested one sided inequality.

The assembly has the statement of the target character for character and has no gap of its
own. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Height step. The lower cut `10 ^ 100 ≤ T` implies `1 ≤ T`, which is the height
condition used by the shared two sided estimate of the weighted zero count. -/
theorem book_zero_count_high_far_height
    {T : ℝ} (hT100 : 10 ^ 100 ≤ T) : 1 ≤ T := by
  exact le_trans (by norm_num) hT100

/-- LEAF. Absolute estimate step. For a primitive character and every height at least one,
the absolute difference between the weighted zero count and the main term is at most the
error term. This is the shared two sided estimate specialized only by its height condition. -/
theorem book_zero_count_high_far_absolute
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  exact book_zero_count χ hχ hT

/-- LEAF. Upper estimate step. An absolute error bound gives the requested upper bound on the
difference between the weighted zero count and the main term. This is one inequality between
real numbers and uses no further property of the character or the height. -/
theorem book_zero_count_high_far_upper_of_absolute
    (χ : DirichletCharacter ℂ q) {T : ℝ}
    (habs : |bookCount χ T - bookMain q T| ≤ bookError q T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  exact (abs_le.mp habs).2

/-- Assembly of the split, FREE-nv-step task2269. The statement of
`book_zero_count_large_height_upper_tall_level_one_far_scale_high_far` character for
character, proved from the three leaves with no gap of its own. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_high_far_F2269
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT6 : 10 ^ 6 ≤ T)
    (hq1 : q = 1) (hT100 : 10 ^ 100 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hT' : 1 ≤ T := book_zero_count_high_far_height hT100
  have habs : |bookCount χ T - bookMain q T| ≤ bookError q T :=
    book_zero_count_high_far_absolute χ hχ hT'
  exact book_zero_count_high_far_upper_of_absolute χ habs

end LeanLab.HelfgottMajor.ZeroCount1623
