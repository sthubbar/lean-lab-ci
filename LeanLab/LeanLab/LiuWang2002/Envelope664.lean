import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
A negative result about the available elementary envelope.
Source Liu and Wang 2002 page 169 and Schoenfeld 1976 page 356.
This concerns a sufficient proof input. It asserts no failure of a paper theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664

/-- The coarse Mathlib envelope alone does not imply the required sharp bound. -/
theorem coarse_psi_envelope_insufficient :
    ¬ (∀ X Y : ℝ, 0 < X → 0 ≤ Y → Y ≤ (Real.log 4 + 4) * X →
      Y < 1.001093 * X) := by
  intro h
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hbad := h 1 2 (by norm_num) (by norm_num) (by nlinarith)
  norm_num at hbad

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.coarse_psi_envelope_insufficient
