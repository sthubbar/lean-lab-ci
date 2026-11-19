/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2740000 through 2749999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2740000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2740000 through 2749999. -/
def shifts : List ℕ := [6090624, 6313600, 5223936, 5332864, 4462848, 5966848, 92416, 1491840, 5338624, 1136256, 5578368, 4245760, 5032320, 2058496, 305664, 606208, 2429568, 1851136, 330624, 5896960, 3311488, 1552896, 1207296, 2531584, 1218688, 5856384, 1606144, 1940736, 1929856, 2586624, 146560, 368640, 42240, 2190208, 144384, 2262400, 2913408, 1326208, 5760384, 265216, 2855680, 2036224, 604800, 1100416, 819456, 800896, 2391808, 2183680, 1638016, 1506688, 1008768, 0, 1413760, 1178368, 647296, 102528]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7183427 + 2 * t ∧ (7183427 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7183427) (count := 10000)
    (lo := 2) (W := 7203424) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2740000
