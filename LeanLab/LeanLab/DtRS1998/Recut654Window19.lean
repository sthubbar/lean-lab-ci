/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window19

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 19. -/
def shifts19 : List ℕ := [7002880, 6888192, 6696576, 6997120, 6127104, 5910016, 2842624, 5365632, 5823360, 3722752, 3926656, 4093824, 3506944, 1969920, 3386752, 2032896, 4577664, 3515392, 4975744, 3156096, 2530816, 2800512, 2025600, 3270400, 3594112, 4253184, 703744, 1524096, 3078016, 3194112, 2878464, 807040, 1245696, 4519936, 1593600, 2882944, 3604992, 983680, 1227264, 1708672, 3165312, 1679872, 2269056, 1546240, 2806272, 1884544, 4250880, 46336, 2590080, 548224, 991360, 1363200, 1241856, 2764672, 4195840, 1994880, 0, 1304320, 1201024, 1256832, 3237760, 2673024, 2543104, 1664256, 2636544, 3170944, 2311552, 3854464, 3003264, 3217152, 2839680, 2990464, 1273600]

/-- LEAF: Small prime differences for window 19, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts19, s ≤ 7167683 + 2 * t ∧ (7167683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7167683) (count := 100000)
    (lo := 2) (W := 7367680) shifts19 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window19
