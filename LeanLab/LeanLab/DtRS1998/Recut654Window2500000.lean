/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2500000 through 2509999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2500000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2500000 through 2509999. -/
def shifts : List ℕ := [6721024, 6498048, 5631360, 5740288, 5985792, 6374272, 6263808, 2591104, 5439744, 672640, 3320832, 5746048, 2682880, 1353600, 1733632, 2836992, 6167808, 2669824, 627712, 1937280, 2258560, 1549440, 838528, 1416192, 3718912, 1986048, 6304384, 1543680, 125952, 1821184, 1746432, 16768, 776064, 2337280, 738048, 1273984, 449664, 36352, 202368, 0, 3263104, 4653184, 2597632, 2799232, 1960320, 3196032, 4566528, 2250112, 289408]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7110851 + 2 * t ∧ (7110851 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7110851) (count := 10000)
    (lo := 2) (W := 7130848) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2500000
