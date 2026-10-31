import LeanLab.Zhao2025.CNonnegOrder
import LeanLab.Zhao2025.Section4

/-!
Corollary 3.2 with its monotonicity input discharged and epsilon explicit.
The only cited input is display 3.15 with the actual C and the computed exponent.
Source: Zhao 2025, displays 3.15 to 3.19, page 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.15 alone, for epsilon at most 0.001. -/
theorem cor32_actual_conditional (T : ℝ → ℝ) (epsilon : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 0.001)
    (h315 : ∀ L, 5.2 ≤ L →
      T L ≤ (1 + epsilon) * C 0.029 0.083 0.052 L 0 * Real.exp (-(3334 / 1500 * L))) :
    ∀ L, 5.2 ≤ L → T L ≤ 100 * Real.exp (-2.22 * L) ∧ T L ≤ 0.001 := by
  intro L hL
  have hC : C 0.029 0.083 0.052 L 0 ≤ 99.73 :=
    (C_antitone_nonneg _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) le_rfl hL).trans C319.2
  have hA : (1 + epsilon) * C 0.029 0.083 0.052 L 0 ≤ 100 := by
    calc
      _ ≤ (1 + epsilon) * 99.73 := mul_le_mul_of_nonneg_left hC (by linarith)
      _ ≤ 100 := by nlinarith
  have he : Real.exp (-(3334 / 1500 * L)) ≤ Real.exp (-2.22 * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hb : T L ≤ 100 * Real.exp (-2.22 * L) :=
    (h315 L hL).trans (mul_le_mul hA he (Real.exp_pos _).le (by norm_num))
  exact ⟨hb, hb.trans (LeanLab.Zhao2025.cor32 L hL)⟩

#print axioms cor32_actual_conditional

end LeanLab.Zhao2025.Task56
