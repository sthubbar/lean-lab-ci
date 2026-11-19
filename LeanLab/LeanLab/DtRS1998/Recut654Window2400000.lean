/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2400000 through 2409999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2400000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2400000 through 2409999. -/
def shifts : List ℕ := [6721024, 6498048, 5631360, 5746048, 6374272, 6263808, 2195712, 4653184, 5740288, 776064, 1585792, 3196032, 4108800, 2465920, 5439744, 1626112, 202368, 2682880, 2669824, 407424, 2996352, 672640, 2348160, 1273984, 2994048, 2337280, 2836992, 6304384, 668160, 1286272, 768768, 16768, 1543680, 3718912, 289408, 794880, 2258560, 6167808, 1914112, 125952, 5985792, 2799232, 1621632, 1507840, 1937280, 1416192, 3263104, 2939008, 2250112, 2045440, 1986048, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6910851 + 2 * t ∧ (6910851 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6910851) (count := 10000)
    (lo := 2) (W := 6930848) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2400000
