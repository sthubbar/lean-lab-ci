/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2600000 through 2609999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2600000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2600000 through 2609999. -/
def shifts : List ℕ := [6167040, 5944064, 5431808, 5186304, 5077376, 5820288, 4885760, 5192064, 1794176, 1783296, 5709824, 4099200, 1072128, 1060736, 5613824, 953856, 4316288, 1696128, 458240, 1491456, 1267200, 4012544, 284544, 1345280, 1575936, 2442368, 5750400, 995456, 2642048, 2037120, 1426944, 1192448, 1432064, 459648, 799616, 222080, 3164928, 159104, 1889664, 672896, 1911936, 2128896, 1459584, 825728, 2440064, 2283008, 2115840, 2043648, 989696, 118656, 2709120, 1406336, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6756867 + 2 * t ∧ (6756867 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6756867) (count := 10000)
    (lo := 2) (W := 6776864) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2600000
