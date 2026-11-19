/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2710000 through 2719999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2710000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2710000 through 2719999. -/
def shifts : List ℕ := [6221184, 5485952, 5667968, 5240448, 5131520, 5874432, 5763968, 1837440, 276224, 5246208, 1085952, 1848320, 4153344, 1695872, 2183040, 5998208, 1043840, 1630080, 2696192, 1513728, 2763264, 1114880, 2337152, 2169984, 3219072, 1399424, 1545600, 213248, 2496512, 774144, 3608960, 1126272, 5804544, 268928, 1321344, 727040, 2439168, 172800, 4066688, 1750272, 916352, 4939904, 1758720, 1408640, 4370432, 1943808, 1383680, 1246592, 1121792, 833408, 2820992, 1414272, 1049600, 786432, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7031011 + 2 * t ∧ (7031011 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7031011) (count := 10000)
    (lo := 2) (W := 7051008) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2710000
