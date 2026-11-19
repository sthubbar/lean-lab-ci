/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2300000 through 2309999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2300000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2300000 through 2309999. -/
def shifts : List ℕ := [6161280, 6037504, 5294592, 5967616, 4533504, 5409280, 2346112, 5927040, 4316416, 5102976, 1708672, 2859264, 5403520, 1623552, 290944, 4229760, 439296, 2926336, 1676800, 1016832, 2333056, 5649024, 1913344, 2500224, 2000512, 376320, 70656, 3382144, 1644160, 0, 1921792, 458112, 173184, 86272, 1289344, 5831040, 2984064, 1284864, 2129152, 1484416, 1571712, 1409664, 2260864, 1277952, 501760, 115072, 3772032, 2659584, 1212672]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6374083 + 2 * t ∧ (6374083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6374083) (count := 10000)
    (lo := 2) (W := 6394080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2300000
