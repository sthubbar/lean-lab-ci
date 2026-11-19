/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2350000 through 2359999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2350000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2350000 through 2359999. -/
def shifts : List ℕ := [7170816, 6947840, 6435584, 6195840, 6081152, 6824064, 2787072, 6713600, 1723776, 5889536, 1463424, 1803392, 3645824, 2893440, 285056, 2495232, 4168704, 5320064, 2064512, 6190080, 652160, 1504512, 2349056, 1999232, 5102976, 1288320, 449792, 2363904, 3770624, 2579712, 6617600, 3446144, 1957632, 393984, 3443840, 1993472, 1658112, 1122432, 1162880, 739200, 3388800, 3249024, 4558592, 2430720, 786560, 2387072, 497280, 3132672, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7260643 + 2 * t ∧ (7260643 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7260643) (count := 10000)
    (lo := 2) (W := 7280640) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2350000
