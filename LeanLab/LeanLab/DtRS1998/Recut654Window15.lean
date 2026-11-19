/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window15

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 15. -/
def shifts15 : List ℕ := [6127104, 5910016, 5365632, 3237760, 5823360, 3722752, 4975744, 4577664, 4519936, 3156096, 3515392, 1969920, 807040, 2871552, 4056064, 1092096, 2465152, 4093824, 3926656, 3217152, 3170944, 4250880, 1304320, 1524096, 2842624, 3165312, 1459200, 3939712, 4195840, 1664256, 4452864, 3270400, 46336, 2051712, 3854464, 3242880, 2530816, 2032896, 3594112, 652800, 1273600, 1227264, 548224, 3604992, 1241856, 1201024, 1756672, 1706496, 1546240, 1994880, 3194112, 781312, 983680, 2673024, 703744, 2590080, 1766784, 2806272, 1884544, 3700480, 2764672, 2839680, 891904, 2636544, 1342720, 3003264, 1293184, 2878464, 2311552, 1708672, 0]

/-- LEAF: Small prime differences for window 15, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts15, s ≤ 6367683 + 2 * t ∧ (6367683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6367683) (count := 100000)
    (lo := 2) (W := 6567680) shifts15 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window15
