/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2750000 through 2759999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2750000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2750000 through 2759999. -/
def shifts : List ℕ := [6093312, 5540096, 5358080, 5118336, 5746560, 5003648, 5636096, 4025472, 4812032, 1417728, 2209280, 1105920, 725888, 1709568, 110336, 1193472, 987008, 210816, 1568000, 998400, 1838208, 3938816, 1271552, 1963392, 2693120, 44928, 705536, 2311296, 1502208, 1255808, 5870336, 1622400, 5676672, 915968, 658560, 148352, 2635392, 2055168, 993920, 2366336, 1280768, 880128, 921728, 3091200, 1630848, 2368640, 1969920, 85376, 5112576, 4242560, 1385856, 1332608, 427008, 141056, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6983139 + 2 * t ∧ (6983139 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6983139) (count := 10000)
    (lo := 2) (W := 7003136) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2750000
