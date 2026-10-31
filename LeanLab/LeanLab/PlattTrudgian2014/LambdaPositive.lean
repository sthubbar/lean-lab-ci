/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 3 display 5, positive lambda convention.
The infimum uses the repaired measure criterion and does not assert attainment.
-/
import LeanLab.PlattTrudgian2014.LambdaTwo

namespace LeanLab.PlattTrudgian2014

noncomputable def lambdaPositiveThreshold (c : ℝ) : ℝ :=
  sInf {lam : ℝ | 0 < lam ∧ LambdaOK c lam}

theorem lambdaPositiveThreshold_eq (c : ℝ) : lambdaPositiveThreshold c = lambdaThreshold c := by
  apply le_antisymm
  · apply le_csInf (s := {lam : ℝ | 0 ≤ lam ∧ LambdaOK c lam})
    · exact ⟨1, by norm_num, lambdaOK_one c⟩
    · intro lam hlam
      apply le_of_forall_pos_le_add
      intro ε hε
      apply csInf_le (s := {lam : ℝ | 0 < lam ∧ LambdaOK c lam})
      · exact ⟨0, fun _ h => h.1.le⟩
      · exact ⟨by linarith [hlam.1], lambdaOK_mono (by linarith) hlam.2⟩
  · apply le_csInf (s := {lam : ℝ | 0 < lam ∧ LambdaOK c lam})
    · exact ⟨1, by norm_num, lambdaOK_one c⟩
    · intro lam hlam
      exact lambdaThreshold_le hlam.1.le hlam.2

theorem lambdaPositiveThreshold_nonneg (c : ℝ) : 0 ≤ lambdaPositiveThreshold c := by
  rw [lambdaPositiveThreshold_eq]
  exact lambdaThreshold_nonneg c

theorem lambdaPositiveThreshold_uncond_h2 : lambdaPositiveThreshold (109 / 154) ≤ 0.88592 := by
  rw [lambdaPositiveThreshold_eq]
  exact lambdaThreshold_uncond_h2

theorem lambdaPositiveThreshold_GRH_h2 : lambdaPositiveThreshold (1 / 2) ≤ 0.75881 := by
  rw [lambdaPositiveThreshold_eq]
  exact lambdaThreshold_GRH_h2

#print axioms lambdaPositiveThreshold_eq
#print axioms lambdaPositiveThreshold_nonneg
#print axioms lambdaPositiveThreshold_uncond_h2
#print axioms lambdaPositiveThreshold_GRH_h2

end LeanLab.PlattTrudgian2014
