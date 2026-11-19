/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2570000 through 2579999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2570000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2570000 through 2579999. -/
def shifts : List ℕ := [5952256, 5729280, 5217024, 5605504, 5495040, 4977280, 4862592, 1901056, 1481344, 1130496, 1914112, 4101504, 4971520, 4670976, 3340032, 439552, 1244800, 1217280, 1822336, 2227584, 2068224, 817024, 774912, 1489792, 1426944, 1212160, 1114752, 3884416, 5399040, 285952, 517504, 243456, 814080, 505216, 1361152, 0, 2030464, 780672, 3797760, 2950144, 2427264, 1697152, 1568512, 1276672, 1191552, 1139712, 1674880, 977664, 5535616, 2552064, 1168512, 852864, 845952, 739072, 244864]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6482083 + 2 * t ∧ (6482083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6482083) (count := 10000)
    (lo := 2) (W := 6502080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2570000
