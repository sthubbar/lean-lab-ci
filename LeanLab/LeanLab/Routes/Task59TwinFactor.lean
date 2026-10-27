/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The elementary reciprocal local factor needed by the sharper U1436 plan.
-/
import Mathlib

namespace LeanLab.Routes.Task59

/-- The reciprocal twin factor is the exact local factor in the U1436 plan. -/
theorem twin_factor_inv_eq (p : ℝ) (hp : 2 < p) :
    (1 - 1 / (p - 1) ^ 2)⁻¹ = (p - 1) ^ 2 / (p * (p - 2)) := by
  have hpred : p - 1 ≠ 0 := by linarith
  have hf : 1 - 1 / (p - 1) ^ 2 = p * (p - 2) / (p - 1) ^ 2 := by
    field_simp [hpred] <;> ring
  rw [hf, inv_div]

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.twin_factor_inv_eq
