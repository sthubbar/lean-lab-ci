/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window1

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 1. -/
def shifts1 : List ℕ := [3515392, 3452544, 3506944, 3156096, 3237760, 3140352, 3242880, 3386752, 3217152, 3078016, 2025600, 2990464, 1524096, 807040, 2636544, 3594112, 3165312, 1810816, 1664256, 703744, 1593600, 3270400, 3003264, 46336, 2590080, 3302272, 2032896, 734464, 2483712, 1546240, 354816, 2530816, 2673024, 1884544, 2610432, 1273600, 1227264, 2764672, 1766784, 991360, 1679872, 1241856, 1808640, 2842624, 3604992, 413056, 483456, 0, 2465152, 891904, 1382784, 1924992, 1304320, 1293184, 2269056, 2839680, 1092096, 2270464, 2543104, 1342720, 1201024, 1363200, 1256832, 2311552, 2800512, 1708672, 1969920]

/-- LEAF: Small prime differences for window 1, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts1, s ≤ 3567683 + 2 * t ∧ (3567683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 3567683) (count := 100000)
    (lo := 2) (W := 3767680) shifts1 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window1
