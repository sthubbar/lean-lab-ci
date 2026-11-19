/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2410000 through 2419999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2410000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2410000 through 2419999. -/
def shifts : List ℕ := [6271360, 6048384, 5536128, 5924608, 5181696, 1595776, 5814144, 5296384, 4990080, 1808896, 2746368, 563968, 5718144, 3269248, 3659136, 824320, 1094016, 5290624, 1746048, 836608, 1563904, 263424, 1449600, 50176, 0, 2220160, 1680256, 1296768, 4203520, 1487616, 388864, 1458816, 758656, 2544384, 1136128, 1165056, 2489344, 1171968, 1800448, 562560, 2141440, 4420608, 222976, 2813440, 60288, 2546688, 2147968, 2016256, 1371520, 4116864, 2871168, 2387328, 2349568, 1898496]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6481187 + 2 * t ∧ (6481187 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6481187) (count := 10000)
    (lo := 2) (W := 6501184) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2410000
