/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window14

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 14. -/
def shifts14 : List ℕ := [6127104, 5910016, 5365632, 4975744, 5823360, 3386752, 3237760, 4452864, 1706496, 3515392, 1546240, 1092096, 3854464, 3165312, 4519936, 1459200, 3170944, 4577664, 1304320, 3156096, 3594112, 3140352, 3926656, 3242880, 4056064, 1524096, 2530816, 2610432, 3939712, 2878464, 807040, 0, 2465152, 2871552, 1201024, 1363200, 4195840, 1241856, 3847936, 1593600, 2270464, 3003264, 1293184, 3217152, 2311552, 1245696, 991360, 4250880, 3078016, 2032896, 46336, 2839680, 1994880, 891904, 2764672, 2051712, 2269056, 1756672, 2636544, 1969920, 1679872, 1273600, 413056, 1664256, 1227264, 483456, 3270400, 2806272, 1884544, 2842624, 1924992, 1708672, 983680]

/-- LEAF: Small prime differences for window 14, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts14, s ≤ 6167683 + 2 * t ∧ (6167683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6167683) (count := 100000)
    (lo := 2) (W := 6367680) shifts14 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window14
