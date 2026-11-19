/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window13

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 13. -/
def shifts13 : List ℕ := [5910016, 5823360, 5365632, 4975744, 4452864, 3386752, 3237760, 1706496, 4577664, 3515392, 4195840, 2871552, 4519936, 1969920, 3156096, 2465152, 891904, 2673024, 1546240, 3165312, 1092096, 46336, 2882944, 3242880, 2878464, 3270400, 354816, 3170944, 3217152, 3594112, 1459200, 3926656, 1766784, 4056064, 1256832, 1273600, 2269056, 1679872, 2806272, 1929472, 1524096, 983680, 2543104, 2025600, 3604992, 3847936, 3452544, 734464, 483456, 991360, 1363200, 1241856, 3506944, 4093824, 1708672, 2311552, 0, 3854464, 4250880, 1810816, 3194112, 1304320, 2590080, 1293184, 2530816, 2800512, 1382784, 2636544, 3078016, 1664256]

/-- LEAF: Small prime differences for window 13, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts13, s ≤ 5967683 + 2 * t ∧ (5967683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 5967683) (count := 100000)
    (lo := 2) (W := 6167680) shifts13 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window13
