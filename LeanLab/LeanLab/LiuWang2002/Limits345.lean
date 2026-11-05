import Mathlib

/-!
Task345. Negative results for attempted replacements of the cited inputs.
These diagnose insufficient proof bounds. They assert no paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345
open Real

/-- Derived diagnostic for the prime power expansion used on Schoenfeld page 356.
Replacing every theta of a root by that root gives an insufficient tail bound
at X equal to 512. The seven roots from the third through the ninth already
sum to more than three cube roots. This concerns the scalar envelope. -/
theorem root_envelope_counterexample : 3 * (512 : ℝ) ^ (1 / 3 : ℝ) <
    (512 : ℝ) ^ (1 / 3 : ℝ) + (512 : ℝ) ^ (1 / 4 : ℝ) +
      (512 : ℝ) ^ (1 / 5 : ℝ) + (512 : ℝ) ^ (1 / 6 : ℝ) +
        (512 : ℝ) ^ (1 / 7 : ℝ) + (512 : ℝ) ^ (1 / 8 : ℝ) +
          (512 : ℝ) ^ (1 / 9 : ℝ) := by
  have h3 : (8 : ℝ) ≤ (512 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h4 : (4.5 : ℝ) ≤ (512 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h5 : (3.4 : ℝ) ≤ (512 : ℝ) ^ (1 / 5 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h6 : (2.8 : ℝ) ≤ (512 : ℝ) ^ (1 / 6 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h7 : (2.4 : ℝ) ≤ (512 : ℝ) ^ (1 / 7 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h8 : (2.1 : ℝ) ≤ (512 : ℝ) ^ (1 / 8 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have h9 : (2 : ℝ) ≤ (512 : ℝ) ^ (1 / 9 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  have hc : (512 : ℝ) ^ (1 / 3 : ℝ) ≤ 8 := by
    rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    norm_num [Real.rpow_natCast]
  linarith

/-- Derived diagnostic for the prime log sum estimate on Liu and Wang page 172.
The lab integer bounds use constants 7 and zero. Their abstract interval
admits candidate values outside the required interval. This concerns
candidate values only. -/
theorem mertens_interval_insufficient (x : ℝ) :
    ∃ s : ℝ, log x - 7 ≤ s ∧ s ≤ log x ∧
      ¬(log x - 1.385 ≤ s ∧ s ≤ log x - 1.28) := by
  refine ⟨log x, by linarith, le_rfl, ?_⟩
  intro h
  linarith [h.2]

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.root_envelope_counterexample
#print axioms LeanLab.LiuWang2002.Task345.mertens_interval_insufficient
