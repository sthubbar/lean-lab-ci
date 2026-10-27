/-
AI wrote this Lean code for CODEX task58.
Polynomial enclosures for a finer integral certificate in P0039 equation 3.9.
Binary Goldbach is open.
-/
import Mathlib

open Real Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The logarithm polynomial obtained from the series at one. -/
def logPoly (n : ℕ) (q : ℝ) : ℝ := -∑ i ∈ range n, (-q) ^ (i + 1) / (i + 1)

/-- The finite geometric sum for the reciprocal kernel. -/
def geomPoly (n : ℕ) (q : ℝ) : ℝ := ∑ i ∈ range n, q ^ i

/-- A uniform logarithm remainder bound on a nonnegative interval below one. -/
theorem logPoly_error {q a : ℝ} (hq : 0 ≤ q) (hqa : q ≤ a) (ha : a < 1) (n : ℕ) :
    |log (1 + q) - logPoly n q| ≤ a ^ (n + 1) / (1 - a) := by
  have hq1 : |(-q)| < 1 := by rw [abs_neg, abs_of_nonneg hq]; linarith
  have h := abs_log_sub_add_sum_range_le hq1 n
  rw [abs_neg, abs_of_nonneg hq, sub_neg_eq_add] at h
  have he : |log (1 + q) - logPoly n q| =
      |(∑ i ∈ range n, (-q) ^ (i + 1) / (i + 1)) + log (1 + q)| := by
    congr 1
    unfold logPoly
    ring
  rw [he]
  exact h.trans (div_le_div₀ (pow_nonneg (hq.trans hqa) _)
    (pow_le_pow_left₀ hq hqa _) (by linarith) (by linarith))

/-- Exact geometric remainder, before taking absolute values. -/
theorem geomPoly_remainder {q : ℝ} (hq : q ≠ 1) (n : ℕ) :
    geomPoly n q - 1 / (1 - q) = -q ^ n / (1 - q) := by
  unfold geomPoly
  rw [geom_sum_eq hq]
  have h1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have h2 : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
  field_simp
  <;> ring

/-- A uniform geometric remainder bound for positive and negative arguments. -/
theorem geomPoly_error {q a : ℝ} (hqa : |q| ≤ a) (ha : a < 1) (n : ℕ) :
    |geomPoly n q - 1 / (1 - q)| ≤ a ^ n / (1 - a) := by
  have ha0 : 0 ≤ a := (abs_nonneg q).trans hqa
  have hq1 : q < 1 := ((le_abs_self q).trans hqa).trans_lt ha
  rw [geomPoly_remainder (ne_of_lt hq1), abs_div, abs_neg, abs_pow,
    abs_of_pos (sub_pos.mpr hq1)]
  exact div_le_div₀ (pow_nonneg ha0 _) (pow_le_pow_left₀ (abs_nonneg q) hqa _)
    (by linarith) (by linarith [le_abs_self q])

/-- Sixty logarithm terms give a uniform error below two billionths. -/
theorem logPoly60_error {q : ℝ} (hq : 0 ≤ q) (hqa : q ≤ 7 / 10) :
    |log (1 + q) - logPoly 60 q| ≤ (2 / 1000000000 : ℝ) := by
  have h := logPoly_error hq hqa (by norm_num : (7 / 10 : ℝ) < 1) 60
  refine h.trans ?_
  norm_num

/-- Seventy geometric terms give a uniform error below one ten billionth. -/
theorem geomPoly70_error {q : ℝ} (hqa : |q| ≤ 7 / 10) :
    |geomPoly 70 q - 1 / (1 - q)| ≤ (1 / 10000000000 : ℝ) := by
  have h := geomPoly_error hqa (by norm_num : (7 / 10 : ℝ) < 1) 70
  refine h.trans ?_
  norm_num

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.logPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.geomPoly_remainder
#print axioms LeanLab.ChenPrimeExceptional.Task58.geomPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.logPoly60_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.geomPoly70_error
