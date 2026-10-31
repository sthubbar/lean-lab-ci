/-
Almost equal ternary Goldbach with window √n for odd 7 ≤ n < 10000, assembled from the
kernel range checks AERange1 to AERange7. See IDEAS I-0014. A finite range only.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.Ternary.AERange1
import LeanLab.Ternary.AERange2
import LeanLab.Ternary.AERange3
import LeanLab.Ternary.AERange4
import LeanLab.Ternary.AERange5
import LeanLab.Ternary.AERange6
import LeanLab.Ternary.AERange7

namespace LeanLab.Ternary

/-- Every odd `n` with `7 ≤ n < 10000` is a sum of three primes each within `√n` of `n/3`.
Kernel-checked, zero sorry. A finite range only. -/
theorem almostEqual_sqrt_upTo_10000 (n : ℕ) (ho : Odd n) (h7 : 7 ≤ n) (hn : n < 10000) :
    IsAlmostEqualTernary n ((n : ℝ) ^ (1 / 2 : ℝ)) := by
  rw [← Real.sqrt_eq_rpow]
  have ho' : n % 2 = 1 := Nat.odd_iff.mp ho
  by_cases c0 : n < 1000
  · exact aeRange_sound 7 993 aeRange_7 n (by omega) (by omega) ho'
  by_cases c1 : n < 2000
  · exact aeRange_sound 1000 1000 aeRange_1000 n (by omega) (by omega) ho'
  by_cases c2 : n < 3000
  · exact aeRange_sound 2000 1000 aeRange_2000 n (by omega) (by omega) ho'
  by_cases c3 : n < 4000
  · exact aeRange_sound 3000 1000 aeRange_3000 n (by omega) (by omega) ho'
  by_cases c4 : n < 5000
  · exact aeRange_sound 4000 1000 aeRange_4000 n (by omega) (by omega) ho'
  by_cases c5 : n < 6000
  · exact aeRange_sound 5000 1000 aeRange_5000 n (by omega) (by omega) ho'
  by_cases c6 : n < 7000
  · exact aeRange_sound 6000 1000 aeRange_6000 n (by omega) (by omega) ho'
  by_cases c7 : n < 8000
  · exact aeRange_sound 7000 1000 aeRange_7000 n (by omega) (by omega) ho'
  by_cases c8 : n < 9000
  · exact aeRange_sound 8000 1000 aeRange_8000 n (by omega) (by omega) ho'
  by_cases c9 : n < 9500
  · exact aeRange_sound 9000 500 aeRange_9000 n (by omega) (by omega) ho'
  by_cases c10 : n < 10000
  · exact aeRange_sound 9500 500 aeRange_9500 n (by omega) (by omega) ho'
  omega

end LeanLab.Ternary
