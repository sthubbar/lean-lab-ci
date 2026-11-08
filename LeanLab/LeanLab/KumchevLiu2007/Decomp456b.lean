import LeanLab.KumchevLiu2007.Novelty1612

/-!
The parameter window preceding display 68 on page 19 of arXiv:0801.0130.
This gives a necessary restriction for that written argument.
It does not supply the circle method or the numerical sieve bounds.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task456

/-- Page 19 before display 68 and page 3 improvement remark.
For positive epsilon, theta2 = 0.595 - 2 epsilon is in the written window
if and only if epsilon is below 7/1200. -/
theorem theta2_window_iff {ε : ℝ} (hε : 0 < ε) :
    (7 / 12 < 595 / 1000 - 2 * ε ∧ 595 / 1000 - 2 * ε ≤ 2 / 3) ↔
      ε < 7 / 1200 := by
  constructor
  · intro h
    linarith [h.1]
  · intro h
    constructor <;> linarith

end LeanLab.KumchevLiu2007.Task456

#print axioms LeanLab.KumchevLiu2007.Task456.theta2_window_iff
