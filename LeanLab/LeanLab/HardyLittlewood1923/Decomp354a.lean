import LeanLab.HardyLittlewood1923.Decomp296Evaluation

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 25 equations 3.151 to 3.155.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354a

open Real
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp105

/-- P0004 page 25 equations 3.151 to 3.155.
The exact model evaluation target follows from the proved task296 bound. -/
theorem farey_to_finite :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖fareyModel n - (finiteMain n : ℂ)‖ ≤
        C * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n ^ B := by
  obtain ⟨C, _, hC⟩ := Decomp296Evaluation.farey_to_finite_bound
  exact ⟨2, C, 4, hC⟩

#print axioms farey_to_finite

end LeanLab.HardyLittlewood1923.Decomp354a
