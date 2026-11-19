/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2580000 through 2589999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2580000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2580000 through 2589999. -/
def shifts : List ℕ := [6986496, 6763520, 5896832, 3984384, 6529280, 938112, 5705216, 2246400, 5135744, 6639744, 6011520, 4374272, 2856576, 6433280, 1645184, 2515584, 532736, 2935296, 2602752, 1880192, 4918656, 3259520, 1887104, 2709120, 1814912, 282240, 3461504, 1999104, 715136, 0, 6251264, 6569856, 2948352, 2225792, 2524032, 2173952, 1277696, 2279040, 3102464, 819456, 1851264, 2086656, 1003520, 6005760, 1473792, 2613632, 1619072, 3586304, 2310912, 2202752, 688512]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7536323 + 2 * t ∧ (7536323 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7536323) (count := 10000)
    (lo := 2) (W := 7556320) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2580000
