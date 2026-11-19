/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window12

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 12. -/
def shifts12 : List ℕ := [5365632, 4975744, 4519936, 4250880, 4452864, 4195840, 3939712, 1524096, 3926656, 4253184, 652800, 3594112, 3270400, 3604992, 4056064, 1706496, 3242880, 1304320, 1766784, 2764672, 3156096, 891904, 2806272, 3847936, 1256832, 1708672, 0, 734464, 2673024, 3078016, 807040, 3194112, 1245696, 3170944, 2878464, 3386752, 2032896, 1273600, 1593600, 3302272, 2269056, 2530816, 3165312, 3722752, 3003264, 983680, 4577664, 2465152, 354816, 1810816, 2871552, 2842624, 2800512, 991360, 2025600, 46336, 483456, 3506944, 2990464, 1227264, 1808640, 1664256, 1241856, 3237760, 1546240, 781312, 3217152, 2636544, 1924992, 1929472, 2590080, 3515392, 3854464, 5823360]

/-- LEAF: Small prime differences for window 12, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts12, s ≤ 5767683 + 2 * t ∧ (5767683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 5767683) (count := 100000)
    (lo := 2) (W := 5967680) shifts12 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window12
