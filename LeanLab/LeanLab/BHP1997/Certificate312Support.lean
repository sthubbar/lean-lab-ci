/-
P0069, page 51. Exact support reduction for the fixed E2 grid.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical

/-- Page 51. Omit columns outside the two exact affine support bounds.
This is auxiliary finite bookkeeping for the existing whole-cell grid. -/
theorem lowerTwo_row_support_sum (i : ℕ) :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j) =
      ∑ j ∈ Finset.range (min 4096 (min (i+2)
        ((409600000 - (lowerTwoGridPoint i + 2*51195904))/75002+1))),
        lowerTwoGridWeight i j := by
  symm
  apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
  intro j hj hnot
  simp only [Finset.mem_range, not_lt] at hj hnot
  have hz : lowerTwoGridPoint i + 37501 < lowerTwoGridPoint j ∨
      409600000 < lowerTwoGridPoint i + 2 * lowerTwoGridPoint j := by
    simp only [lowerTwoGridPoint] at *
    omega
  unfold lowerTwoGridWeight
  rw [if_pos hz]

end LeanLab.BHP1997.DecompC165d
