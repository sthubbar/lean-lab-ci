/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2460000 through 2469999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2460000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2460000 through 2469999. -/
def shifts : List ℕ := [6635136, 6412160, 6288384, 6081920, 3110144, 2251392, 5660160, 4022912, 5353856, 4567296, 2109824, 2172672, 5545472, 1540224, 5654400, 250880, 363776, 365952, 4784384, 3633024, 2262272, 2044032, 1660544, 1895040, 2164224, 4480640, 181376, 6218496, 1813376, 1927680, 1140992, 2910464, 1647744, 927744, 6177920, 586752, 582272, 1200384, 1851392, 1247360, 413952, 3234944, 2853120, 2583936, 2380032, 1528832, 1496960, 2751104, 2505216, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6944963 + 2 * t ∧ (6944963 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6944963) (count := 10000)
    (lo := 2) (W := 6964960) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2460000
