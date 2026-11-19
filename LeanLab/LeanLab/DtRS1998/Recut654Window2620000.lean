/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2620000 through 2629999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2620000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2620000 through 2629999. -/
def shifts : List ℕ := [6625024, 6402048, 5889792, 2586880, 5644288, 680064, 6071808, 1530112, 1787520, 5650048, 1447680, 576640, 2900352, 3167104, 3622912, 311424, 355840, 2740992, 1884928, 2252160, 2703232, 353664, 617088, 2347648, 1489792, 5535360, 4557184, 171264, 1725184, 572160, 3100032, 2369920, 531712, 240768, 29952, 1112320, 4470528, 2033920, 1177984, 1864320, 403840, 4774272, 1949440, 193408, 1803264, 1525632, 2843008, 1190272, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7254851 + 2 * t ∧ (7254851 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7254851) (count := 10000)
    (lo := 2) (W := 7274848) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2620000
