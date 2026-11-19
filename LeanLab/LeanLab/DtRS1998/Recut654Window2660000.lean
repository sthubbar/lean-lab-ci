/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2660000 through 2669999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2660000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2660000 through 2669999. -/
def shifts : List ℕ := [6635136, 6081920, 5899904, 5654400, 6177920, 6288384, 5545472, 1188096, 2596992, 690176, 5660160, 1822592, 1540224, 321536, 6412160, 2164224, 1421952, 5353856, 3177216, 3110144, 1797632, 2380032, 2583936, 2109824, 1200384, 627200, 2357760, 1140992, 424064, 1647744, 4567296, 3234944, 1499904, 926336, 2910464, 1959552, 250880, 2853120, 3633024, 365952, 1735296, 1293824, 20480, 4480640, 541824, 2751104, 708992, 4022912, 1927680, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7344963 + 2 * t ∧ (7344963 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7344963) (count := 10000)
    (lo := 2) (W := 7364960) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2660000
