/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 185 Corollary 2, exactly the existing PRThreeFifthsInput.
The elementary leaves are shared with Decomp125.
-/
import LeanLab.PlattTrudgian2014.Decomp125

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- LEAF. P0026 pages 184 to 185, display 7.1 and Corollary 2.
The majorant and finite matrix calculation must give the strict three fifths pressure gap.
Theorem 2 then supplies the uniform norm moment bound after enlarging A. -/
theorem pr_three_fifths_moment_certificate125 :
    ∃ t A b : ℝ, 0 < t ∧ 0 ≤ A ∧
      b < t * 0.7894008449792309 - (3 / 5) * Real.log 2 ∧
      ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        A * Real.exp (b * L) := by
  sorry

/-- Assembly of P0026 page 185 Corollary 2, exactly the existing cited Prop.
CONDITIONAL ON the open numerical moment certificate. -/
theorem pr_three_fifths_decomposed125 : PRThreeFifthsInput := by
  obtain ⟨t, A, b, ht, hA, hgap, hm⟩ := pr_three_fifths_moment_certificate125
  apply powerLogBound_of_exp_decay125 hA (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (by linarith : (3 / 5 : ℝ) * Real.log 2 < t * 0.7894008449792309 - b)
  intro N _
  exact large_values_of_norm_moment125 ht hm N

#print axioms pr_three_fifths_moment_certificate125
#print axioms pr_three_fifths_decomposed125

end LeanLab.PlattTrudgian2014
