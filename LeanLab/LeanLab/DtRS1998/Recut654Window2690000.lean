/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2690000 through 2699999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2690000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2690000 through 2699999. -/
def shifts : List ℕ := [6161280, 6384256, 5649024, 5409280, 6037504, 1016832, 5102976, 1921792, 5831040, 3382144, 4316416, 2859264, 1708672, 4229760, 5403520, 1277952, 1913344, 1562496, 115072, 5294592, 2333056, 2984064, 2602240, 1284864, 439296, 1289344, 215040, 2129152, 2011392, 1676800, 2926336, 2657280, 2000512, 1858944, 890112, 112896, 86272, 1396864, 1649280, 2462464, 1079424, 2254336, 676864, 401280, 0, 4533504, 1623552, 717952, 3772032, 2659584, 2346112, 2260864, 1171072]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7154083 + 2 * t ∧ (7154083 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7154083) (count := 10000)
    (lo := 2) (W := 7174080) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2690000
