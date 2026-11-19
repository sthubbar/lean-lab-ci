/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2360000 through 2369999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2360000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2360000 through 2369999. -/
def shifts : List ℕ := [6384256, 6161280, 5649024, 5403520, 1206912, 2346112, 5927040, 1249024, 5409280, 1562496, 1212672, 6037504, 4316416, 4533504, 5102976, 1793152, 432000, 2926336, 675456, 3382144, 335872, 2659584, 676864, 5294592, 70656, 1676800, 401280, 937216, 1546752, 1171072, 4229760, 2011392, 2602240, 2500224, 2106880, 2254336, 112896, 1708672, 1600512, 5967616, 173184, 2260864, 501760, 1577344, 1042944, 1921792, 5831040, 3772032, 2984064, 2333056, 1623552, 717952, 439296, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6494083 + 2 * t ∧ (6494083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6494083) (count := 10000)
    (lo := 2) (W := 6514080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2360000
