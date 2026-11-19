/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2390000 through 2399999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2390000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2390000 through 2399999. -/
def shifts : List ℕ := [6313600, 6090624, 5338624, 5578368, 5966848, 5223936, 5760384, 4245760, 5032320, 800896, 1851136, 604800, 5332864, 5856384, 2429568, 3311488, 387456, 2855680, 2036224, 2913408, 1136256, 2058496, 4159104, 878848, 42240, 2262400, 1940736, 361344, 1929856, 606208, 3701376, 2588928, 1722496, 1506688, 866560, 0, 1573504, 1552896, 819456, 220288, 102528, 431104, 1606144, 1788288, 1638016, 2391808, 1529856, 1413760, 1339008, 2190208, 2183680, 1207296]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6483427 + 2 * t ∧ (6483427 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6483427) (count := 10000)
    (lo := 2) (W := 6503424) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2390000
