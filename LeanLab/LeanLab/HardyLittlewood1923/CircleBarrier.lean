import Mathlib

/-!
AI wrote this Lean code for CODEX task52.
This records the exponent barrier of the existing U1503 circle method route.
It does not assert a barrier for the paper's different generating function route.
-/

namespace LeanLab.HardyLittlewood1923.Task52

lemma circle_exponent_comparison (Θ : ℝ) :
    2 - (1 - Θ) / 17 ≤ 2 + (Θ - 3 / 4) ↔ 47 / 64 ≤ Θ := by
  constructor <;> intro h <;> linarith

lemma circle_exponent_too_large {Θ : ℝ} (hΘ : Θ < 47 / 64) :
    2 + (Θ - 3 / 4) < 2 - (1 - Θ) / 17 := by
  linarith

#print axioms circle_exponent_comparison
#print axioms circle_exponent_too_large

end LeanLab.HardyLittlewood1923.Task52
