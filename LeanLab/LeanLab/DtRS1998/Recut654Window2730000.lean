/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2730000 through 2739999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2730000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2730000 through 2739999. -/
def shifts : List ℕ := [6635136, 6177920, 5545472, 6288384, 5660160, 5899904, 2251392, 1813376, 3234944, 3177216, 1463552, 2596992, 5353856, 5654400, 1540224, 1900160, 2910464, 2380032, 181376, 4567296, 1647744, 2262272, 6412160, 1200384, 3110144, 1188096, 1247360, 10112, 2357760, 752640, 541824, 2109824, 1528832, 468096, 6081920, 2713344, 1457792, 927744, 337152, 690176, 2853120, 321536, 2172672, 1797632, 363776, 2511744, 1735296, 4784384, 2505216, 708992, 6218496, 2908160, 2164224, 1330304, 1122432, 682880, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7484963 + 2 * t ∧ (7484963 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7484963) (count := 10000)
    (lo := 2) (W := 7504960) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2730000
