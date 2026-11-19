/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window11

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 11. -/
def shifts11 : List ℕ := [5365632, 4975744, 4519936, 4250880, 4253184, 4195840, 3515392, 1241856, 4452864, 3700480, 1756672, 3217152, 3926656, 652800, 3854464, 3156096, 2530816, 3165312, 3270400, 3003264, 2839680, 602752, 1293184, 1524096, 3604992, 703744, 1808640, 3722752, 991360, 4577664, 1706496, 734464, 3847936, 3452544, 3140352, 2311552, 2032896, 2842624, 2465152, 2269056, 1256832, 46336, 2878464, 1342720, 1363200, 2270464, 1766784, 2543104, 1929472, 2800512, 2806272, 1304320, 1459200, 781312, 1664256, 413056, 3506944, 1924992, 3237760, 1245696, 807040, 0, 2871552, 891904, 3302272, 1382784, 3170944, 2590080, 1273600, 1092096, 2673024, 2095360, 4093824, 3939712]

/-- LEAF: Small prime differences for window 11, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts11, s ≤ 5567683 + 2 * t ∧ (5567683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 5567683) (count := 100000)
    (lo := 2) (W := 5767680) shifts11 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window11
