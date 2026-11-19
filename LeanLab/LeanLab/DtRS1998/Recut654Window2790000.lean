/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2790000 through 2799999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2790000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2790000 through 2799999. -/
def shifts : List ℕ := [5753856, 5864320, 5121408, 6211072, 5236096, 5475840, 4929792, 5230336, 2327040, 4143232, 698368, 228096, 2753152, 1039488, 1748608, 4360320, 1933696, 1389312, 5988096, 3208960, 1075840, 843648, 1470976, 0, 5657856, 997888, 5794432, 1398528, 1503616, 1685760, 1404160, 1072896, 158208, 1827328, 2159872, 266112, 1476096, 2429056, 2172928, 1236480, 2081152, 823296, 1838208, 117760, 258816, 1740160, 1619968, 1311232, 1111680, 2810880, 1955968, 1450368, 502272, 1223680, 1116160]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7180899 + 2 * t ∧ (7180899 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7180899) (count := 10000)
    (lo := 2) (W := 7200896) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2790000
