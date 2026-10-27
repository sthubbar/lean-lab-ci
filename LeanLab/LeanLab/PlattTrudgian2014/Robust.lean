/-
The two "not admissible" results of Statements.lean hold across the paper's whole range
for C₀ and C₂: 0.6601618158 < C₀ < 0.6601618159, 1.93642 < C₂ < 1.93656. Point raised by
the VERIFY subagent of run 20261016T2003Z-5561.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Statements

namespace LeanLab.PlattTrudgian2014

theorem rhs_le_of (C₀ C₂ C₃ c B : ℝ) (h0 : 0 < C₀) (h0' : C₀ ≤ 0.6601618159)
    (h2 : 1.93642 ≤ C₂) (hc : 0 < c) (hC3 : 0 < C₃)
    (hB : C₃ < B * ((7.8209 - 2) * 1.93642 + c / 0.6601618159 * 0.6931471803)) :
    rhs C₀ 7.8209 C₂ C₃ c < B := by
  unfold rhs
  have hl := Real.log_two_gt_d9
  have hcc : c / 0.6601618159 ≤ c / C₀ := div_le_div_of_nonneg_left hc.le h0 h0'
  have hd : (7.8209 - 2) * 1.93642 + c / 0.6601618159 * 0.6931471803 ≤
      (7.8209 - 2) * C₂ + c / C₀ * Real.log 2 := by
    have : c / 0.6601618159 * 0.6931471803 ≤ c / C₀ * Real.log 2 :=
      mul_le_mul hcc hl.le (by norm_num) (by positivity)
    nlinarith
  have hpos : 0 < (7.8209 - 2) * 1.93642 + c / 0.6601618159 * 0.6931471803 := by positivity
  rw [div_lt_iff₀ (hpos.trans_le hd)]
  have hB0 : 0 < B := by
    by_contra hneg; push_neg at hneg; nlinarith
  nlinarith

/-- Unconditionally K = 11 fails for every C₀, C₂ in the paper's ranges. -/
theorem not_admissible_11_all (C₀ C₂ : ℝ) (h0 : 0.6601618158 < C₀) (h0' : C₀ < 0.6601618159)
    (h2 : 1.93642 < C₂) :
    ¬ Admissible 0.8594 C₀ 7.8209 C₂ 3.02858417 (109 / 154) 11 := by
  unfold Admissible
  have := rhs_le_of C₀ C₂ 3.02858417 (109 / 154) 0.2521 (by linarith) h0'.le h2.le
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

/-- On GRH K = 6 fails for every C₀, C₂ in the paper's ranges. -/
theorem not_admissible_6_GRH_all (C₀ C₂ : ℝ) (h0 : 0.6601618158 < C₀)
    (h0' : C₀ < 0.6601618159) (h2 : 1.93642 < C₂) :
    ¬ Admissible 0.7163436 C₀ 7.8209 C₂ 3.011112 (1 / 2) 6 := by
  unfold Admissible
  have := rhs_le_of C₀ C₂ 3.011112 (1 / 2) 0.2553 (by linarith) h0'.le h2.le
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

end LeanLab.PlattTrudgian2014
