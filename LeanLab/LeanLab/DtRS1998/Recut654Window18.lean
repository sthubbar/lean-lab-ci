/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window18

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 18. -/
def shifts18 : List ℕ := [6888192, 6997120, 6696576, 5910016, 6127104, 7002880, 2842624, 5823360, 3722752, 5365632, 3926656, 4093824, 3506944, 1808640, 3594112, 1241856, 4519936, 1994880, 2311552, 4253184, 4975744, 2871552, 3270400, 1706496, 703744, 2673024, 3939712, 3604992, 46336, 0, 983680, 2025600, 2764672, 1245696, 891904, 2636544, 2530816, 3140352, 1708672, 4577664, 1969920, 1546240, 1810816, 3217152, 1363200, 3854464, 1929472, 1256832, 1304320, 3156096, 3078016, 1227264, 2270464, 2610432, 2032896, 3386752, 2990464, 4452864, 3003264, 1293184, 3302272, 1593600, 4056064, 3165312, 1924992, 2465152, 1756672, 1092096, 3515392, 2269056, 2839680]

/-- LEAF: Small prime differences for window 18, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts18, s ≤ 6967683 + 2 * t ∧ (6967683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6967683) (count := 100000)
    (lo := 2) (W := 7167680) shifts18 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window18
