/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2610000 through 2619999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2610000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2610000 through 2619999. -/
def shifts : List ℕ := [6431616, 5878400, 3429504, 5341952, 4580864, 4363776, 1756032, 6208640, 5456640, 5150336, 1969152, 2706944, 722816, 918912, 2973696, 1594112, 1724160, 2547584, 47360, 2509824, 1444224, 5696384, 6014976, 1670912, 2047872, 1609856, 0, 1043840, 210432, 2704640, 2649600, 2906624, 2380416, 486656, 996864, 505472, 162432, 1906304, 1531776, 6084864, 937472, 1457024, 479360, 2301696, 1691520, 1336704, 3031424, 2154240, 1064192, 5450880, 2393472, 2058752, 1696640, 1325312, 984576, 220544]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7041443 + 2 * t ∧ (7041443 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7041443) (count := 10000)
    (lo := 2) (W := 7061440) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2610000
