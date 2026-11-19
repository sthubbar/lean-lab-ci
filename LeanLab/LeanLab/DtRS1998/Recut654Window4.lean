/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window4

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 4. -/
def shifts4 : List ℕ := [4093824, 3926656, 4056064, 3242880, 3939712, 3217152, 3847936, 2871552, 4195840, 3156096, 3594112, 3452544, 2025600, 3700480, 1706496, 2990464, 3604992, 2543104, 0, 3270400, 3003264, 3722752, 2269056, 2530816, 1256832, 2882944, 1593600, 1304320, 2673024, 3515392, 1363200, 3170944, 2032896, 2764672, 3165312, 3078016, 4253184, 1273600, 1241856, 3386752, 3194112, 734464, 2590080, 2800512, 1201024, 983680, 483456, 413056, 1245696, 3237760, 1884544, 2483712, 1766784, 2878464, 781312, 2806272, 1342720, 2839680, 2270464, 3140352, 2311552, 1227264, 2842624, 1808640, 4250880]

/-- LEAF: Small prime differences for window 4, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts4, s ≤ 4167683 + 2 * t ∧ (4167683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 4167683) (count := 100000)
    (lo := 2) (W := 4367680) shifts4 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window4
