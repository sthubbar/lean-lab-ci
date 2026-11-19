/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2540000 through 2549999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2540000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2540000 through 2549999. -/
def shifts : List ℕ := [6704256, 6481280, 6357504, 5614592, 4853504, 5729280, 6247040, 1491072, 1804416, 1882496, 1943552, 5723520, 2113152, 250496, 2233344, 721280, 1597952, 1716864, 1604864, 6287616, 1920512, 2028672, 5422976, 30720, 2666112, 1729664, 3246336, 109184, 19584, 2320512, 752000, 2580864, 651392, 493184, 4636416, 4092032, 4549760, 2449152, 2820224, 2922240, 2241792, 2653056, 2331392, 1897344, 1526912, 390656, 2574336, 1566080, 5969024, 3702144, 2426880, 1996800, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7174083 + 2 * t ∧ (7174083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7174083) (count := 10000)
    (lo := 2) (W := 7194080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2540000
