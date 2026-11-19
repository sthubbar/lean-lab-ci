/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window5

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 5. -/
def shifts5 : List ℕ := [3840128, 3782784, 3837824, 3434880, 3526656, 3191936, 3680768, 3513600, 3181056, 1293440, 3643008, 2804096, 3287424, 2743040, 1612544, 2130048, 2117760, 3039488, 891264, 2458496, 3441408, 828800, 2829824, 3102336, 2857344, 2465408, 1343616, 1856000, 2727296, 2577408, 1353728, 2973696, 843776, 2664960, 950144, 0, 1111040, 321408, 832640, 189696, 2824704, 2177024, 1516416, 1180544, 1133184, 2259968, 1397760, 1581824, 2752256, 2429568, 1898496, 2223488, 2469888, 1046144, 4039808, 2052096, 1295616, 290688, 1511936, 3309696, 1556864, 2781056, 1471488, 4106880, 2590208, 1857408, 814208, 880128, 1266816, 969728]

/-- LEAF: Small prime differences for window 5, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts5, s ≤ 3954627 + 2 * t ∧ (3954627 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 3954627) (count := 100000)
    (lo := 2) (W := 4154624) shifts5 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window5
