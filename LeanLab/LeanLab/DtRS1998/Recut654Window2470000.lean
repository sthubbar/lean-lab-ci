/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2470000 through 2479999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2470000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2470000 through 2479999. -/
def shifts : List ℕ := [7196544, 6973568, 6461312, 6215808, 6106880, 6849792, 975360, 6739328, 5915264, 2725632, 2812800, 2374784, 6779904, 3796352, 511872, 1213568, 1270400, 3158400, 2024960, 3145344, 1251584, 561408, 6643328, 2941440, 445952, 1314048, 2209152, 677888, 460544, 5128704, 1487744, 6221568, 3312512, 3066624, 5042048, 210048, 927360, 4584320, 1749504, 4194432, 2671232, 0, 742784, 3274752, 2823680, 1702400, 1683840, 5345792, 3073152, 2097152, 925184]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7526371 + 2 * t ∧ (7526371 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7526371) (count := 10000)
    (lo := 2) (W := 7546368) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2470000
