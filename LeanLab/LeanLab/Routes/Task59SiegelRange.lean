/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
An elementary range check for the parameter in the cited MM14 input.
Source: MM printed page 1 equation 1 and printed page 3 Theorem 1.4.
-/
import LeanLab.Routes.U1451MMSiegel

namespace LeanLab.Routes.Task59

/-- The displayed Siegel zero parameter lies strictly between 4 over 5 and 1. -/
theorem mm14_beta_range (q : ℕ) (η : ℝ) (hq : 2 ≤ q) (hη : 10 ≤ η) :
    (4 / 5 : ℝ) < 1 - 1 / (η * Real.log q) ∧ 1 - 1 / (η * Real.log q) < 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : (1 / 2 : ℝ) < Real.log q :=
    lt_of_lt_of_le (by linarith [Real.log_two_gt_d9])
      (Real.log_le_log (by norm_num) hqR)
  have hm := mul_le_mul_of_nonneg_right hη (show 0 ≤ Real.log q by linarith)
  have hd : 5 < η * Real.log q := by linarith
  have hi : 0 < (1 : ℝ) / (η * Real.log q) := one_div_pos.mpr (by linarith)
  have hs : (1 : ℝ) / (η * Real.log q) < 1 / 5 :=
    one_div_lt_one_div_of_lt (by norm_num) hd
  constructor <;> linarith

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.mm14_beta_range
