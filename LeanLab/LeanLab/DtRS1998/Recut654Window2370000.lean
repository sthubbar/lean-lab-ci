/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2370000 through 2379999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2370000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2370000 through 2379999. -/
def shifts : List ℕ := [6635136, 6412160, 5899904, 5654400, 6288384, 6081920, 1797632, 2172672, 5660160, 1813376, 5545472, 3177216, 4784384, 2164224, 6177920, 1959552, 1528832, 1200384, 321536, 2357760, 1874432, 2583936, 2751104, 413952, 690176, 6218496, 1535744, 1421952, 627200, 541824, 2853120, 1457792, 2109824, 582272, 2596992, 0, 3633024, 1851392, 2505216, 2251392, 1330304, 1927680, 363776, 116480, 968832, 5353856, 652160, 2511744, 1647744]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6764963 + 2 * t ∧ (6764963 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6764963) (count := 10000)
    (lo := 2) (W := 6784960) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2370000
