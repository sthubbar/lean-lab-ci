/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2530000 through 2539999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2530000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2530000 through 2539999. -/
def shifts : List ℕ := [6776832, 6553856, 5801856, 5687168, 6430080, 6041600, 4708992, 6319616, 2101248, 1955072, 4926080, 5796096, 3774720, 5495552, 728448, 6223616, 1670528, 1876992, 40832, 0, 3251840, 1110528, 2499456, 1993088, 3318912, 4622336, 1969920, 3052160, 1342080, 1435520, 2185728, 831872, 2069376, 4164608, 3049856, 2521728, 1939328, 1641600, 1282688, 609792, 2738688, 1068032, 894336, 2892800, 2653440, 1681920, 723968, 2994816, 1409408]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7226659 + 2 * t ∧ (7226659 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7226659) (count := 10000)
    (lo := 2) (W := 7246656) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2530000
