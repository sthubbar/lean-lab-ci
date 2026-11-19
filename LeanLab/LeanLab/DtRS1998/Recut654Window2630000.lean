/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2630000 through 2639999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2630000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2630000 through 2639999. -/
def shifts : List ℕ := [5820288, 5944064, 5077376, 6167040, 5186304, 4316288, 1345280, 720000, 5709824, 2128896, 4885760, 1575936, 2642048, 5192064, 732288, 3554816, 1179648, 4012544, 1889664, 2766848, 0, 2442368, 1704576, 240896, 1406336, 1072128, 5613824, 1696128, 1641728, 458240, 4099200, 1426944, 2709120, 2283008, 1060736, 500736, 1432064, 2043648, 5750400, 1383296, 1354496, 5431808, 1267200, 953856, 1067648, 799616, 2037120, 1192448, 222080, 3164928, 2115840, 1028864, 989696]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6816867 + 2 * t ∧ (6816867 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6816867) (count := 10000)
    (lo := 2) (W := 6836864) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2630000
