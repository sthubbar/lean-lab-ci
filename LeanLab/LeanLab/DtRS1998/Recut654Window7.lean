/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window7

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 7. -/
def shifts7 : List ℕ := [4577664, 4519936, 4195840, 4250880, 3515392, 4452864, 3217152, 3854464, 3156096, 3594112, 3700480, 3140352, 3847936, 2839680, 3506944, 1664256, 3926656, 4253184, 3165312, 1304320, 1524096, 3722752, 2878464, 891904, 652800, 46336, 2610432, 3170944, 2465152, 3242880, 483456, 2543104, 1924992, 807040, 1245696, 2530816, 3003264, 1756672, 1593600, 983680, 1256832, 3939712, 1766784, 1884544, 2269056, 2025600, 2764672, 1201024, 1352832, 991360, 0, 3270400, 1546240, 1363200, 734464, 4093824, 3194112, 1342720, 2673024, 1929472, 1810816, 2806272, 3078016, 2590080, 703744, 1969920, 1382784, 3604992, 2842624, 2311552, 1994880, 1273600, 4056064]

/-- LEAF: Small prime differences for window 7, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts7, s ≤ 4767683 + 2 * t ∧ (4767683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 4767683) (count := 100000)
    (lo := 2) (W := 4967680) shifts7 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window7
