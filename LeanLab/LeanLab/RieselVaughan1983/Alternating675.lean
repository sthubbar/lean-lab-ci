import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
The alternating series remainder used on page 53 of Riesel and Vaughan 1983.
This supplies the scalar remainder bound, not the logarithmic integral evaluation.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Finset Filter
open scoped Topology

namespace LeanLab.RieselVaughan1983.Task675

/-- Page 53 bounds the alternating reciprocal-square series between zero
and its first term. The indexing starts at zero here, with exponent n + 1. -/
theorem alternating_reciprocal_square_bounds (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ ∑' n : ℕ, (-1 : ℝ) ^ n *
      (2 / (z ^ (n + 1) * ((n : ℝ) + 1) ^ 2)) ∧
    (∑' n : ℕ, (-1 : ℝ) ^ n *
      (2 / (z ^ (n + 1) * ((n : ℝ) + 1) ^ 2))) ≤ 2 / z := by
  let f : ℕ → ℝ := fun n => 2 / (z ^ (n + 1) * ((n : ℝ) + 1) ^ 2)
  have hz0 : 0 < z := by linarith
  have hb : Summable (fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left (2 : ℝ)
  have hs : Summable f := by
    apply hb.of_nonneg_of_le (fun n => by dsimp [f]; positivity)
    intro n
    dsimp [f]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hz)
  have ha : Antitone f := by
    intro n m hnm
    dsimp [f]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hp : z ^ (n + 1) ≤ z ^ (m + 1) :=
      pow_le_pow_right₀ hz (Nat.add_le_add_right hnm 1)
    have hnmR : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by gcongr
    exact mul_le_mul hp hsq (by positivity) (by positivity)
  have ht := hs.tendsto_alternating_series_tsum
  have hlo := Antitone.alternating_series_le_tendsto ht ha 0
  have hhi := Antitone.tendsto_le_alternating_series ht ha 0
  constructor
  · simpa using hlo
  · simpa [f] using hhi

end LeanLab.RieselVaughan1983.Task675
