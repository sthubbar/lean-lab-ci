/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2680000 through 2689999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2680000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2680000 through 2689999. -/
def shifts : List ℕ := [6625024, 6071808, 5889792, 5644288, 1130880, 6278272, 6167808, 2586880, 5343744, 2495104, 5650048, 5535360, 1190272, 680064, 576640, 4774272, 2154112, 4012800, 6402048, 4557184, 3100032, 742528, 2252160, 2033920, 1237248, 1917568, 1525632, 3622912, 327040, 698880, 672768, 3167104, 2501632, 2900352, 2241280, 1650432, 3224832, 1884928, 1530112, 1453440, 1890048, 2703232, 1447680, 1725184, 1411840, 455808, 355840, 2099712, 6208384, 2843008, 2369920, 2162560, 1803264, 1486848, 531712, 353664, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7374851 + 2 * t ∧ (7374851 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7374851) (count := 10000)
    (lo := 2) (W := 7394848) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2680000
