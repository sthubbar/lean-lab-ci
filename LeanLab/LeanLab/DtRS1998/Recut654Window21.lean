/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window21

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 21. -/
def shifts21 : List ℕ := [7561216, 7520640, 7242624, 7002880, 6888192, 3939712, 7424640, 4975744, 6696576, 6997120, 5910016, 6127104, 1929472, 1241856, 2882944, 2871552, 3722752, 3156096, 1201024, 2800512, 1304320, 5365632, 3847936, 4253184, 3700480, 2590080, 4056064, 1524096, 3078016, 3604992, 1756672, 1706496, 3594112, 3140352, 703744, 1994880, 2636544, 1708672, 0, 3237760, 548224, 3003264, 3515392, 1256832, 1293184, 5823360, 4519936, 1342720, 4452864, 2878464, 2270464, 354816, 2806272, 2465152, 781312, 1664256, 3270400, 2311552, 1969920, 2842624, 2483712, 4577664, 3302272, 2673024, 602752, 1546240, 413056, 1382784, 3165312, 3194112, 2543104, 4093824]

/-- LEAF: Small prime differences for window 21, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts21, s ≤ 7567683 + 2 * t ∧ (7567683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7567683) (count := 100000)
    (lo := 2) (W := 7767680) shifts21 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window21
