import LeanLab.HelfgottMajor.Decomp389a
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Elementary supplies for the four split modules received in the final main merge.
Source P0014 page 38 display 4.26 and page 39 very low zero paragraph.
The numerical zero count itself remains a cited input.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454k
open Real Decomp389a ZeroCount1623

/-- The middle range height reduction for P0014 page 38 display 4.26. -/
theorem leaf_mid_t_over_pi_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (_hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    t / π ≤ 2 * exp 1 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hmul := mul_le_mul_of_nonneg_right hq (by linarith : (0 : ℝ) ≤ t)
  apply (div_le_iff₀ pi_pos).mpr
  nlinarith

/-- The middle range logarithm comparison for P0014 page 38 display 4.26. -/
theorem leaf_mid_log_ge (q : ℕ) [NeZero q] (t : ℝ) (_ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (_hhi : q * t ≤ 2 * π * exp 1) :
    log (2 * π) ≤ log (q * t) := by
  exact log_le_log (by positivity) hlo

/-- The middle range scalar margin for P0014 page 38 display 4.26.
This places a supplied count of 13 inside the target budget and proves no zero count.
-/
theorem leaf_mid_constant_margin (q : ℕ) [NeZero q] (t : ℝ) (_ht : 1 ≤ t)
    (htpi : t / π ≤ 2 * exp 1) (hlog : log (2 * π) ≤ log (q * t)) :
    13 ≤ 0.5 * log (q * t) + 17.7 - t / π := by
  linarith [LeanLab.HelfgottMajor.log_two_pi_gt, exp_one_lt_d9]

/-- The very low multiplicity count is summable by finite strip support alone.
Source P0014 page 39, the very low zero paragraph using display 4.26.
-/
theorem very_low_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (_hχ : χ.IsPrimitive) (T : ℝ) (_hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) := by
  exact summable_zeroIdx χ T _

end LeanLab.HelfgottMajor.Decomp454k
