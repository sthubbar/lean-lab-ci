import LeanLab.Zhao2025.Section4

/-!
The variable cutoff in the first case of Section 4.
Source: Zhao 2025, page 13 before display 4.1.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- The paper's cutoff covers every positive first lambda. -/
noncomputable def smallCaseCutoff (l : ℝ) : ℝ := max 5.68 (1.09 * Real.log l⁻¹)

/-- The cutoff is positive and satisfies the exponential condition used in case1_bound. -/
theorem small_case_cutoff_spec (l : ℝ) (hl : 0 < l) :
    5.68 ≤ smallCaseCutoff l ∧ 0 ≤ smallCaseCutoff l ∧
      Real.exp (-(smallCaseCutoff l / 1.09)) ≤ l := by
  have hbase : 5.68 ≤ smallCaseCutoff l := le_max_left _ _
  have hlog : 1.09 * Real.log l⁻¹ ≤ smallCaseCutoff l := le_max_right _ _
  refine ⟨hbase, by linarith, ?_⟩
  rw [Real.log_inv] at hlog
  calc
    _ ≤ Real.exp (Real.log l) := Real.exp_le_exp.mpr (by norm_num [div_eq_mul_inv]; linarith)
    _ = l := Real.exp_log hl

#print axioms small_case_cutoff_spec
end LeanLab.Zhao2025.Task56
