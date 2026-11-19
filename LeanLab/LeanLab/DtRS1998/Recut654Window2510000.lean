/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2510000 through 2519999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2510000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2510000 through 2519999. -/
def shifts : List ℕ := [6732160, 5996928, 6274944, 5757184, 6385408, 5642496, 6178944, 2694016, 5450880, 2348416, 3274240, 1554816, 2261248, 4881408, 5751424, 1344384, 1364736, 2680960, 3331968, 2056576, 1560576, 1297408, 58624, 460800, 2477056, 347904, 1427328, 1285120, 2024704, 806016, 1910400, 1518976, 779904, 2454784, 2206848, 2269696, 1023360, 724224, 1744768, 638848, 3007488, 1625856, 4664320, 4119936, 3730048, 1065856, 565120, 0, 2602240, 1948416, 683776]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7141987 + 2 * t ∧ (7141987 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7141987) (count := 10000)
    (lo := 2) (W := 7161984) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2510000
