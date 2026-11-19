/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2780000 through 2789999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2780000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2780000 through 2789999. -/
def shifts : List ℕ := [6161280, 6384256, 5409280, 5649024, 6037504, 5294592, 5927040, 1921792, 4316416, 70656, 949504, 1042944, 2129152, 4533504, 163072, 401280, 5102976, 1913344, 937216, 2011392, 115072, 890112, 432000, 5967616, 112896, 1396864, 1676800, 331392, 439296, 1484416, 2984064, 335872, 4229760, 2602240, 1284864, 2333056, 1571712, 1644160, 290944, 0, 1016832, 2859264, 2260864, 2106880, 1649280, 1600512, 1171072, 1289344, 1277952, 871552, 2659584, 2657280, 2500224, 2346112, 1793152]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7334083 + 2 * t ∧ (7334083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7334083) (count := 10000)
    (lo := 2) (W := 7354080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2780000
