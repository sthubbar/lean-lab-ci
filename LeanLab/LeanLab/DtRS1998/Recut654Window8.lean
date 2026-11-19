/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window8

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 8. -/
def shifts8 : List ℕ := [4975744, 4577664, 4519936, 4250880, 3194112, 4195840, 3156096, 3939712, 3217152, 3926656, 4452864, 1304320, 1459200, 3594112, 3165312, 4056064, 1664256, 3270400, 3242880, 2530816, 4253184, 2764672, 1524096, 891904, 652800, 3722752, 2032896, 1546240, 1227264, 2270464, 2610432, 991360, 1766784, 46336, 1706496, 2311552, 1924992, 3847936, 2839680, 2543104, 983680, 1382784, 1363200, 3237760, 2806272, 602752, 1245696, 1273600, 483456, 1929472, 2800512, 548224, 3003264, 2590080, 3515392, 2990464, 3452544, 807040, 1092096, 2878464, 2025600, 1679872, 2882944, 3078016, 2095360, 0, 354816, 2465152, 1810816, 1756672, 2051712]

/-- LEAF: Small prime differences for window 8, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts8, s ≤ 4967683 + 2 * t ∧ (4967683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 4967683) (count := 100000)
    (lo := 2) (W := 5167680) shifts8 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window8
