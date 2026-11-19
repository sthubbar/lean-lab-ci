/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2310000 through 2319999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2310000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2310000 through 2319999. -/
def shifts : List ℕ := [6313600, 6090624, 5223936, 5966848, 5578368, 5338624, 5760384, 44416, 5032320, 3311488, 972288, 1851136, 2855680, 1491840, 1573504, 2913408, 1142016, 1929856, 5856384, 1842688, 4462848, 1722496, 604800, 2036224, 1552896, 2262400, 0, 4245760, 2586624, 92416, 1476096, 1178368, 925824, 5332864, 1501056, 2531584, 2183680, 1214208, 3701376, 2391808, 330624, 5896960, 1638016, 946176, 220288, 1207296, 1008768, 146560, 2588928, 1326208, 144384, 15616]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6323427 + 2 * t ∧ (6323427 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6323427) (count := 10000)
    (lo := 2) (W := 6343424) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2310000
