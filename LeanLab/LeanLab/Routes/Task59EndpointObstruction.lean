/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The lab constant 4.45 cannot cover the paper's full range starting at 2.
This is an endpoint obstruction for the lab variant, not an error in the paper.
-/
import LeanLab.Routes.Task59GoldbachDefinition

namespace LeanLab.Routes.Task59

open LeanLab.ChirreHagen2025

/-- No sum of two odd primes lies in the proposed 4.45 interval at x equal to 2. -/
theorem not_goldbach_445_at_two :
    ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ (2 : ℝ) < n ∧
      (n : ℝ) < 2 + 4.45 * Real.log 2 ^ 2 := by
  rintro ⟨n, hn, _, hhi⟩
  have h6 : (6 : ℝ) ≤ n := by
    exact_mod_cast (goldbach_number_even_and_six_le hn).2
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ 0.7 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hsq := pow_le_pow_left₀ hlog0 hlog 2
  nlinarith

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.not_goldbach_445_at_two
