/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2700000 through 2709999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2700000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2700000 through 2709999. -/
def shifts : List ℕ := [6684672, 6461696, 5595008, 5709696, 4833920, 6337920, 6227456, 4616832, 1578368, 1471488, 6131456, 1877760, 413312, 5703936, 2429568, 5403392, 1549440, 2311808, 636288, 5949440, 3226752, 3159680, 2646528, 1190528, 591360, 2960000, 1944576, 739712, 1784832, 1507328, 463488, 1862912, 2213760, 1900928, 0, 1585280, 3682560, 1171968, 2800640, 1949696, 1237632, 2957696, 4072448, 1977216, 1710080, 11136, 4530176, 2561280, 2300928, 1317248, 2554752, 1546496, 975872, 230912]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7474499 + 2 * t ∧ (7474499 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7474499) (count := 10000)
    (lo := 2) (W := 7494496) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2700000
