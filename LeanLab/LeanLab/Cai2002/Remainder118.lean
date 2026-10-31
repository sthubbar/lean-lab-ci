/-
P0044, page 603 display 4.11. A coarse error candidate is too large.
This is a negative result for the coarse proof route.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
open Filter Asymptotics
namespace LeanLab.Cai2002
/-- Strategy check for page 603 display 4.11 and the final scale on page 604.
A square-root-tail candidate at the cutoff N to one over eleven has exponent 21/22.
This candidate is not negligible relative to the bare final power-log scale. -/
theorem coarse_remainder_not_littleO118 : ¬ ((fun x : ℝ => x ^ (21 / 22 : ℝ) * Real.log x ^ 2) =o[atTop]
    (fun x : ℝ => x ^ (0.95 : ℝ) / Real.log x ^ 2)) := by
  intro h
  obtain ⟨x, hb, hx⟩ := ((h.bound (by norm_num : (0 : ℝ) < 0.5)).and
    (eventually_ge_atTop (Real.exp 1))).exists
  have hx1 : 1 ≤ x := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos 1) hx
  have hsq : 1 ≤ Real.log x ^ 2 := by nlinarith
  have hp : 0 < x ^ (0.95 : ℝ) / Real.log x ^ 2 := by positivity
  have hpow : x ^ (0.95 : ℝ) ≤ x ^ (21 / 22 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsmall : x ^ (0.95 : ℝ) / Real.log x ^ 2 ≤ x ^ (0.95 : ℝ) :=
    div_le_self (by positivity) hsq
  have hlarge : x ^ (21 / 22 : ℝ) ≤ x ^ (21 / 22 : ℝ) * Real.log x ^ 2 :=
    le_mul_of_one_le_right (by positivity) hsq
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_pos hp] at hb
  linarith
end LeanLab.Cai2002
