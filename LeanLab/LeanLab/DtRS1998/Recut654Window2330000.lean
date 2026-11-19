/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2330000 through 2339999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2330000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2330000 through 2339999. -/
def shifts : List ℕ := [6684672, 6461696, 5595008, 6337920, 6227456, 5709696, 4833920, 4616832, 5403392, 2222208, 1549440, 1862912, 5703936, 1847168, 2800640, 3682560, 6131456, 2300928, 5949440, 3226752, 1578368, 415488, 371072, 2213760, 802176, 1546496, 2646528, 1923968, 3284480, 6268032, 676736, 1784832, 1944576, 4072448, 1585280, 591360, 732416, 1977216, 2407296, 1710080, 1018368, 0, 1513088, 3159680, 2633472, 1190528, 515456, 2762880, 2311808, 2093568, 1697280, 975872]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6734499 + 2 * t ∧ (6734499 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6734499) (count := 10000)
    (lo := 2) (W := 6754496) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2330000
