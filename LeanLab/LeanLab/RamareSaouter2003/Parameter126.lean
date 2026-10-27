import LeanLab.RamareSaouter2003.Theorem2Row1

/-!
P0099, printed Table 1 row 150 on p. 11.
This checks compatibility of the printed numerical parameters.
It does not refute Theorem 2. The discrepancy remains a QUESTION.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Parameter126

open Real LeanLab.RamareSaouter2003.Row1

/-- At Y = exp 150, the printed alpha2 = 23 times 10^23 cannot satisfy
both the root growth condition and the target interval width.
Source: Table 1 on p. 11 and Theorem 4 on p. 18. -/
theorem row150_parameters_incompatible : ¬ ∃ u : ℝ,
    (23 : ℝ) * 10 ^ 23 ≤ u * √(Real.exp 150) ∧
      u * (1 + (1 - 2 * 0.44536) * 55) ≤ 1 / 212215384 := by
  rintro ⟨u, hroot, hwidth⟩
  have hu : u ≤ 1 / (212215384 * (1 + (1 - 2 * (0.44536 : ℝ)) * 55)) := by
    linarith
  have hs : √(Real.exp 150) = Real.exp 75 := by
    rw [← Real.exp_half]
    norm_num
  rw [hs] at hroot
  have he := (exp_pow_bounds 75 (by norm_num)).2.le
  have hprod : u * Real.exp 75 ≤
      1 / (212215384 * (1 + (1 - 2 * (0.44536 : ℝ)) * 55)) * 2.7182818286 ^ 75 := by
    calc
      u * Real.exp 75 ≤
          1 / (212215384 * (1 + (1 - 2 * (0.44536 : ℝ)) * 55)) * Real.exp 75 :=
            mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)
  have hn : 1 / (212215384 * (1 + (1 - 2 * (0.44536 : ℝ)) * 55)) * 2.7182818286 ^ 75 <
      23 * 10 ^ 23 := by norm_num
  linarith

end LeanLab.RamareSaouter2003.Parameter126
