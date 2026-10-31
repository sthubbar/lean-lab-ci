/-
P0066, page 105, an elementary alternative to the integration estimate before 5.9.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977LogWeights

/-- A logarithmic weight is bounded by the moment exponent used in 2.7. -/
theorem log_le_moment {d : ℝ} (hd : 1 ≤ d) : Real.log d ≤ d ^ (3 / 8 : ℝ) := by
  have hd0 : 0 < d := by linarith
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have ht0 : 0 < d ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hd0 _
  have h := Real.log_le_sub_one_of_pos (div_pos ht0 (Real.exp_pos 1))
  rw [Real.log_div ht0.ne' (Real.exp_pos 1).ne', Real.log_rpow hd0, Real.log_exp] at h
  have h1 : (3 / 8 : ℝ) * Real.log d ≤ d ^ (3 / 8 : ℝ) / Real.exp 1 := by linarith
  have h2 := (le_div_iff₀ (Real.exp_pos 1)).mp h1
  have h3 := mul_le_mul_of_nonneg_right he (Real.log_nonneg hd)
  nlinarith

/-- The reciprocal logarithm estimate for the range d at most x to the power 1/3. -/
theorem reciprocal_bound {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) (htL : 3 * t ≤ L) :
    1 / (L - t) ≤ 1 / L + (3 / 2 : ℝ) * t / L ^ 2 := by
  have hm : 0 < L - t := by linarith
  have he : 1 / L + (3 / 2 : ℝ) * t / L ^ 2 = (L + 3 / 2 * t) / L ^ 2 := by
    field_simp
  rw [he, div_le_div_iff₀ hm (sq_pos_of_pos hL)]
  nlinarith [mul_nonneg ht (sub_nonneg.mpr htL)]

/-- The finite logarithmic sum is controlled by its mass and its 3/8 moment.
The hypotheses on A and B are analytic inputs when this is applied to the paper's f.
-/
theorem weighted_sum_bound {s : Finset ℕ} {a : ℕ → ℝ} {x A B : ℝ}
    (hx : 1 < x) (hd : ∀ d ∈ s, 1 ≤ d)
    (hsmall : ∀ d ∈ s, 3 * Real.log d ≤ Real.log x)
    (ha : ∀ d ∈ s, 0 ≤ a d) (hA : ∑ d ∈ s, a d ≤ A)
    (hB : ∑ d ∈ s, (d : ℝ) ^ (3 / 8 : ℝ) * a d ≤ B) :
    ∑ d ∈ s, a d / Real.log (x / d) ≤ A / Real.log x + (3 / 2 : ℝ) * B / Real.log x ^ 2 := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hp : ∀ d ∈ s, a d / Real.log (x / d) ≤
      a d / Real.log x + (3 / 2 : ℝ) / Real.log x ^ 2 * ((d : ℝ) ^ (3 / 8 : ℝ) * a d) := by
    intro d hds
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd d hds
    have hd0 : (0 : ℝ) < d := by linarith
    have hq := reciprocal_bound hL (Real.log_nonneg hd1) (hsmall d hds)
    rw [Real.log_div (by linarith : x ≠ 0) hd0.ne']
    have hmul := mul_le_mul_of_nonneg_left hq (ha d hds)
    have ha0 := ha d hds
    have hm := mul_le_mul_of_nonneg_left (log_le_moment hd1)
      (show 0 ≤ (3 / 2 : ℝ) / Real.log x ^ 2 * a d by positivity)
    calc
      a d / (Real.log x - Real.log d) = a d * (1 / (Real.log x - Real.log d)) := by ring
      _ ≤ a d * (1 / Real.log x + 3 / 2 * Real.log d / Real.log x ^ 2) := hmul
      _ = a d / Real.log x + (3 / 2 / Real.log x ^ 2 * a d) * Real.log d := by ring
      _ ≤ a d / Real.log x + (3 / 2 / Real.log x ^ 2 * a d) * (d : ℝ) ^ (3 / 8 : ℝ) :=
        add_le_add le_rfl hm
      _ = a d / Real.log x + 3 / 2 / Real.log x ^ 2 * ((d : ℝ) ^ (3 / 8 : ℝ) * a d) := by ring
  calc
    ∑ d ∈ s, a d / Real.log (x / d)
        ≤ ∑ d ∈ s, (a d / Real.log x + (3 / 2 : ℝ) / Real.log x ^ 2 *
          ((d : ℝ) ^ (3 / 8 : ℝ) * a d)) := Finset.sum_le_sum hp
    _ = (∑ d ∈ s, a d) / Real.log x + (3 / 2 : ℝ) / Real.log x ^ 2 *
          ∑ d ∈ s, (d : ℝ) ^ (3 / 8 : ℝ) * a d := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
    _ ≤ A / Real.log x + (3 / 2 : ℝ) * B / Real.log x ^ 2 := by
      have h1 := div_le_div_of_nonneg_right hA hL.le
      have h2 := mul_le_mul_of_nonneg_left hB (show 0 ≤ (3 / 2 : ℝ) / Real.log x ^ 2 by positivity)
      calc
        _ ≤ A / Real.log x + (3 / 2 : ℝ) / Real.log x ^ 2 * B := add_le_add h1 h2
        _ = _ := by ring

example : Real.log (1 : ℝ) ≤ (1 : ℝ) ^ (3 / 8 : ℝ) := log_le_moment le_rfl

end LeanLab.SchnirelmannBounds.Vaughan1977LogWeights

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977LogWeights.log_le_moment
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977LogWeights.reciprocal_bound
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977LogWeights.weighted_sum_bound
