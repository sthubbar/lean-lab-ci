import LeanLab.Halupczok2012.Decomp598Theorem6

/-!
Nonvacuity checks for U-1672 and Halupczok journal Theorems 2.2 and 3.1.
https://doi.org/10.5802/jtnb.839
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Instances

open Finset Filter
open scoped Classical Topology

/-- The modulus Q2 equal to one is admissible on an unbounded endpoint family.
This checks the logarithmic level in journal Theorems 2.2 and 3.1. -/
theorem unit_level_eventually (B : ℝ) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t * t ^ (-(1 / 2) : ℝ) * Real.log t ^ (-B) := by
  have hb := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (Real.exp 1)] with t ht hte
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le hte
  have hL : 0 < Real.log t := by
    have hh := Real.log_le_log (Real.exp_pos 1) hte
    rw [Real.log_exp] at hh
    linarith
  have hbound : Real.log t ^ B ≤ t ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le B),
      abs_of_nonneg (Real.rpow_nonneg ht0.le (1 / 2)), one_mul] using ht
  have he : t * t ^ (-(1 / 2) : ℝ) = t ^ (1 / 2 : ℝ) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht0]; norm_num
  rw [he, Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hL B), one_mul]
  exact hbound

/-- The nontrivial size and modulus hypotheses hold on the unbounded family
X1 equal to X2 equal to Y equal to t, with both cutoffs one and epsilon one sixth. -/
theorem theorem6_hypotheses_eventually (B : ℝ) (a1 : ℤ) :
    ∀ᶠ t : ℝ in atTop,
      1 ≤ t ∧ t ^ (2 / 3 + (1 / 6 : ℝ)) ≤ t ∧
      1 ≤ t ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) ∧
      1 ≤ t * t ^ (-(1 / 2) : ℝ) * Real.log t ^ (-B) ∧ (a1 : ℝ) ≤ t := by
  filter_upwards [unit_level_eventually B, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (a1 : ℝ)] with t hQ2 ht ha
  refine ⟨ht, ?_, ?_, hQ2, ha⟩
  · convert Real.rpow_le_rpow_of_exponent_le ht
      (by norm_num : (2 / 3 + (1 / 6 : ℝ)) ≤ 1) using 1
    rw [Real.rpow_one]
  · have ht0 : 0 < t := by linarith
    rw [← Real.rpow_add ht0]
    norm_num
    exact ht

/-- The concrete window used for the elementary pointwise input is nonempty. -/
theorem pointwise_window_nonempty : 5 ∈ kRange 4 4 := by
  norm_num [kRange]

/-- At the nontrivial cutoff Q1 equal to one, the sealed left side is exactly
that of display 2.4. This checks the first moment interface on page 340. -/
theorem thm6_unit_modulus (X1 X2 Y Q2 : ℝ) (a1 a2 : ℤ) :
    thm6LHS X1 X2 Y 1 Q2 a1 a2 =
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        |binSumAP X2 Y q2 a2 (2 * k) - Sqa (2 * k) q2 a2 * Y| := by
  simp only [thm6LHS, Nat.floor_one, show Icc 1 (1 : ℕ) = {1} by decide,
    sum_singleton, Int.natCast_one, Int.modEq_one, filter_true]
  exact sum_comm

end LeanLab.Halupczok2012.Decomp598Instances
