/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2380000 through 2389999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2380000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2380000 through 2389999. -/
def shifts : List ℕ := [6007936, 5784960, 5272704, 5661184, 4918272, 5032960, 5454720, 3940096, 2482944, 1545472, 5550720, 913024, 1186176, 5027200, 4726656, 1752832, 4157184, 2550016, 1195392, 1969792, 1537024, 2283264, 3853440, 341632, 908544, 495232, 2086144, 1224192, 1267840, 2123904, 1956736, 830592, 573184, 300544, 62976, 3395712, 0, 1884544, 1730560, 1020544, 794752, 1033344, 836352, 5591296, 1108096, 703104, 2225920, 640512, 3005824, 2280960, 1878016, 1482624, 1416832, 1332352, 1272960, 299136, 55680]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6157763 + 2 * t ∧ (6157763 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6157763) (count := 10000)
    (lo := 2) (W := 6177760) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2380000
