/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2450000 through 2459999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2450000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2450000 through 2459999. -/
def shifts : List ℕ := [6704256, 6481280, 5969024, 5729280, 6357504, 2331392, 6151040, 2666112, 5422976, 2574336, 5723520, 5614592, 3179264, 1269504, 4636416, 6247040, 778112, 2028672, 1964160, 1891712, 995456, 2320512, 2922240, 1566080, 2979584, 2653056, 1191552, 3304064, 996864, 1882496, 1526912, 655872, 696320, 19584, 2426880, 1399424, 2782464, 432896, 3246336, 4092032, 2449152, 1943552, 185600, 1257216, 1532672, 1210112, 69120, 250496, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6994083 + 2 * t ∧ (6994083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6994083) (count := 10000)
    (lo := 2) (W := 7014080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2450000
