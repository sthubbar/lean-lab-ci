/-
P0070 page 362, display 20, scalar audits of the remaining Shiu input.
These compare upper bound envelopes. They give no lower bound for an actual divisor sum.
The earlier blocked fallback routes stay blocked. Their obstruction is made explicit here.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.PerelliPintz1992.Decomp544c
open Real Filter Topology

/-- Page 362, auxiliary audit. A fixed positive power loss in a pointwise divisor bound
exceeds every constant multiple of the required cubic logarithm eventually. -/
theorem pointwise_divisor_envelope_obstruction (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ (3 : ℝ) < x ^ δ := by
  have ho := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hδ).const_mul_left C
  have hp : ∀ᶠ x : ℝ in atTop, 0 < ‖x ^ δ‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact norm_pos_iff.mpr (Real.rpow_pos_of_pos hx δ).ne'
  have hb := ho.eventuallyLT_norm_of_eventually_pos hp
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hpos : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at hx
  exact (le_abs_self _).trans_lt hx

/-- Page 362, auxiliary audit at the shortest allowed interval scale x equal to y cubed.
An initial segment envelope x log cubed x is larger than C y log cubed x when y squared exceeds C. -/
theorem whole_interval_divisor_envelope_obstruction {y C : ℝ} (hy : 1 < y) (hC : C < y ^ 2) :
    C * y * Real.log (y ^ 3) ^ 3 < y ^ 3 * Real.log (y ^ 3) ^ 3 := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hl : 0 < Real.log (y ^ 3) := Real.log_pos (one_lt_pow₀ hy (by norm_num : 3 ≠ 0))
  have hp : 0 < y * Real.log (y ^ 3) ^ 3 := mul_pos hy0 (pow_pos hl 3)
  have hh := mul_lt_mul_of_pos_right hC hp
  convert hh using 1 <;> ring

#print axioms pointwise_divisor_envelope_obstruction
#print axioms whole_interval_divisor_envelope_obstruction
end LeanLab.PerelliPintz1992.Decomp544c
