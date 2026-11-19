/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2430000 through 2439999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2430000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2430000 through 2439999. -/
def shifts : List ℕ := [6384256, 6161280, 5649024, 6037504, 5294592, 5403520, 5927040, 1921792, 2926336, 70656, 5409280, 2984064, 1913344, 1571712, 5831040, 2000512, 1042944, 2106880, 439296, 871552, 5102976, 1396864, 2500224, 2254336, 1277952, 2333056, 112896, 1289344, 2602240, 331392, 4533504, 1171072, 5967616, 1409664, 2346112, 676864, 401280, 2011392, 335872, 1623552, 1284864, 1079424, 949504, 4316416, 2129152, 0, 3382144, 2657280, 290944, 215040, 1858944]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6634083 + 2 * t ∧ (6634083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6634083) (count := 10000)
    (lo := 2) (W := 6654080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2430000
