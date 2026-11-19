/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2440000 through 2449999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2440000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2440000 through 2449999. -/
def shifts : List ℕ := [6518656, 6295680, 5428992, 6171904, 5783424, 5543680, 6061440, 1843072, 1696896, 5537920, 465792, 6102016, 2047744, 4667904, 5965440, 2467456, 5237376, 3516544, 2134912, 2791680, 2793984, 4450816, 2145792, 1927552, 1757952, 1005952, 87040, 2634624, 1778560, 573696, 2388736, 2993664, 811264, 1993344, 2056192, 1412352, 809856, 1305472, 1783680, 852352, 2241280, 1071616, 307584, 247296, 1811200, 1711744, 0, 4364160, 3118464, 2596864, 1544064]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6788483 + 2 * t ∧ (6788483 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6788483) (count := 10000)
    (lo := 2) (W := 6808480) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2440000
