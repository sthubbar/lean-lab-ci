/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
A concrete instance of the interval conclusion. This proves no analytic input.
-/
import LeanLab.ChirreHagen2025.Statements

namespace LeanLab.Routes.Task59

open LeanLab.ChirreHagen2025

/-- The endpoint x equal to 3 admits the odd prime sum 6 in the strict interval. -/
theorem goldbach_445_at_three :
    ∃ n : ℕ, IsGoldbachNumber n ∧ (3 : ℝ) < n ∧
      (n : ℝ) < 3 + 4.45 * Real.log 3 ^ 2 := by
  refine ⟨6, ⟨3, 3, Nat.prime_three, Nat.prime_three, by decide, by decide, rfl⟩,
    by norm_num, ?_⟩
  have hlog : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  change (6 : ℝ) < 3 + 4.45 * Real.log 3 ^ 2
  nlinarith [sq_nonneg (Real.log 3 - 1)]

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.goldbach_445_at_three
