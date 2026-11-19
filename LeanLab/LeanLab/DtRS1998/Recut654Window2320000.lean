/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2320000 through 2329999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2320000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2320000 through 2329999. -/
def shifts : List ℕ := [6684672, 6461696, 5949440, 6337920, 6131456, 5709696, 5595008, 2646528, 5403392, 5703936, 4833920, 2633472, 6227456, 2009088, 1862912, 1249920, 2311808, 4616832, 1847168, 1589760, 4530176, 1171968, 3284480, 739712, 802176, 2159360, 1549440, 6268032, 975872, 415488, 591360, 1949696, 1317248, 2093568, 636288, 4072448, 1578368, 49536, 2213760, 701696, 253056, 1585280, 1872128, 1784832, 1018368, 3159680, 1944576, 3682560, 2960000, 1923968, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6714499 + 2 * t ∧ (6714499 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6714499) (count := 10000)
    (lo := 2) (W := 6734496) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2320000
