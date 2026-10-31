import LeanLab.Zhao2025.CMonotone

/-!
An epsilon retaining variant of display 3.13 with monotonicity discharged.
The input is the epsilon retaining count bound derived from display 3.4.
C is fixed to the actual printed formula.
Source: Zhao 2025, displays 3.12 and 3.13, page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON the epsilon retaining variant of display 3.12.
No monotonicity hypothesis remains. -/
theorem eq313_actual_conditional (N : ℝ → ℝ) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (h312 : ∀ L, 1.311 ≤ L →
      N L ≤ (1 + epsilon) * C (1 / 12) (1 / 4) (1 / 6) L (1 / 2) * Real.exp (8 / 3 * L)) :
    ∀ L, 1.311 ≤ L → N L ≤ (1 + epsilon) * 19.62 * Real.exp (8 / 3 * L) := by
  apply eq313_conditional N (fun L => C (1 / 12) (1 / 4) (1 / 6) L (1 / 2)) epsilon he h312
  · intro L hL
    exact C_antitone _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hL
  · rfl

#print axioms eq313_actual_conditional

end LeanLab.Zhao2025.Task56
