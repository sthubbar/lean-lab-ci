/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2520000 through 2529999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2520000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2520000 through 2529999. -/
def shifts : List ℕ := [6704256, 5969024, 6151040, 5729280, 6357504, 6247040, 2320512, 5422976, 1526912, 4636416, 1569024, 1336832, 2666112, 759296, 5723520, 6481280, 821760, 4853504, 1866752, 3246336, 30720, 1362944, 390656, 2233344, 1943552, 655872, 79232, 19584, 2653056, 4549760, 1882496, 1609344, 1037952, 4092032, 1969280, 2820224, 996864, 1729664, 2574336, 2426880, 1604864, 2241792, 1964160, 1891712, 1491072, 651392, 2178944, 1897344, 1804416, 2977280, 2028672, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7134083 + 2 * t ∧ (7134083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7134083) (count := 10000)
    (lo := 2) (W := 7154080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2520000
