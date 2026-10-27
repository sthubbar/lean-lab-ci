/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
An elementary obstruction to replacing the BPT error by the HSW error
in the U6806 input. This compares majorants and asserts no error in a paper.
-/
import LeanLab.ChirreHagen2025.Lemma26BPT
import LeanLab.ChirreHagen2025.Lemma26HSW

namespace LeanLab.Routes.Task59

open Real LeanLab.ChirreHagen2025

/-- At the input threshold the HSW error exceeds the BPT error by more than 6. -/
theorem bpt_error_add_six_lt_hsw_at_threshold :
    Lemma26B.Rt ((10 : ℝ) ^ 13) + 6 < Lemma26H.Rt ((10 : ℝ) ^ 13) := by
  have hL0 : 0 < log ((10 : ℝ) ^ 13) :=
    lt_of_lt_of_le (by norm_num) Lemma26B.log_1e13
  have hL : log ((10 : ℝ) ^ 13) ≤ 31 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 13)
      (by norm_num : (10 : ℝ) ^ 13 ≤ 2 ^ 44)
    simp only [Real.log_pow] at h ⊢
    norm_num at h ⊢
    nlinarith [Real.log_two_lt_d9]
  have hLL := Lemma26B.loglog_le hL0
  have hR : (0.2 : ℝ) / 10 ^ 13 ≤ 0.2 := by norm_num
  unfold Lemma26B.Rt Lemma26H.Rt
  norm_num at hL hLL hR ⊢
  linarith only [hL, hLL, hR]

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.bpt_error_add_six_lt_hsw_at_threshold
