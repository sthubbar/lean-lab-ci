/-
AI wrote this Lean code. Binary Goldbach is open.
P0024 page 6 Section 3 lambda bound unconditionally.
-/
import LeanLab.PlattTrudgian2014.Lambda
import LeanLab.PlattTrudgian2014.LambdaBounds
import LeanLab.PlattTrudgian2014.Decomp125

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- LEAF. P0024 page 6 Section 3 unconditional limit.
The majorant and finite matrix calculation must give the strict pressure gap. -/
theorem pt_lambda_uncond_certificate289 :
    ∃ t A b : ℝ, 0 < t ∧ 0 ≤ A ∧
      b < t * 0.8594 - (109 / 154) * Real.log 2 ∧
      ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        A * Real.exp (b * L) := by
  sorry

/-- Assembly of P0024 page 6 Section 3, exactly the cited unconditional limit.
CONDITIONAL ON the open numerical moment certificate. -/
theorem pt_lambda_uncond_decomposed289 : LambdaOK (109 / 154) 0.8594 := by
  obtain ⟨t, A, b, ht, hA, hgap, hm⟩ := pt_lambda_uncond_certificate289
  have hgap_real : (109 / 154 : ℝ) * Real.log 2 < t * 0.8594 - b := by linarith
  have hpos : 0 ≤ t * 0.8594 - b := by
    calc
      0 ≤ (109 / 154 : ℝ) * Real.log 2 := by positivity
      _ ≤ t * 0.8594 - b := by linarith
  apply lambdaOK_of_exp_decay hA hpos hgap_real
  intro N _
  exact large_values_of_norm_moment125 ht hm N

end LeanLab.PlattTrudgian2014
