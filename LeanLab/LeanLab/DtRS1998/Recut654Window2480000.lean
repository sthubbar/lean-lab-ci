/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2480000 through 2489999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2480000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2480000 through 2489999. -/
def shifts : List ℕ := [6431616, 6208640, 6084864, 5341952, 5974400, 5456640, 5696384, 984576, 162432, 5150336, 1296384, 3819392, 5450880, 4580864, 2176512, 1609856, 2380416, 1254272, 1960704, 5878400, 2547584, 3429504, 1969152, 1260032, 1696640, 2154240, 1457024, 133632, 160256, 2393472, 2973696, 3031424, 1090304, 2301696, 4277120, 1756032, 486656, 1724160, 479360, 4363776, 448640, 1670912, 1531776, 210432, 118016, 6014976, 2706944, 2509824, 1218432, 2704640, 383232, 220544, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6781443 + 2 * t ∧ (6781443 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6781443) (count := 10000)
    (lo := 2) (W := 6801440) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2480000
