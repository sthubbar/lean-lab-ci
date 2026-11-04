/-
Unit U-1614, run 20261104T0803Z-26516. Refutation of `theorem_6_abstract_bounds`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Halupczok2012.Statements

namespace LeanLab.Halupczok2012.Audit1614
open Finset

theorem thm6LHS_nonneg (X1 X2 Y Q1 Q2 : ℝ) (a1 a2 : ℤ) : 0 ≤ thm6LHS X1 X2 Y Q1 Q2 a1 a2 := by
  unfold thm6LHS
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

/-- The old `theorem_6_abstract_bounds`: every real `C` was allowed. `C = -1`, `A = 0`,
`X1 = X2 = Y = 2`, `Q1 = Q2 = 1`, `c1 = 0`, `c2`, `c3` large. -/
theorem old_theorem_6_abstract_bounds_false :
    ¬ ∀ (A ε B c1 c2 c3 C Y0 X1 X2 Y Q1 Q2 : ℝ) (a1 a2 : ℤ),
      Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y → Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y → 1 ≤ Q1 →
      Q1 ≤ c2 * Y ^ (3 / 2 : ℝ) * X1 ^ (-(1 / 2) : ℝ) → 1 ≤ Q2 →
      Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) → (a1 : ℝ) ≤ X1 →
      thm6LHS X1 X2 Y Q1 Q2 a1 a2 ≤ C * Y ^ 2 * Real.log Y ^ (-A) := by
  intro h
  have hp : (0 : ℝ) < (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have hq : (0 : ℝ) < 2 * (2 : ℝ) ^ (-(1 / 2) : ℝ) * Real.log 2 ^ (-(0 : ℝ)) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have := h 0 0 0 0 (1 / ((2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 2) : ℝ)))
    (1 / (2 * (2 : ℝ) ^ (-(1 / 2) : ℝ) * Real.log 2 ^ (-(0 : ℝ)))) (-1) 0 2 2 2 1 1 0 0
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) le_rfl
    (by have e := div_mul_cancel₀ (1 : ℝ) hp.ne'; rw [mul_assoc]; exact e.ge)
    le_rfl
    (by
      have e := div_mul_cancel₀ (1 : ℝ) hq.ne'
      calc (1 : ℝ) ≤ _ := e.ge
        _ = _ := by ring)
    (by norm_num)
  have h0 := thm6LHS_nonneg 2 2 2 1 1 0 0
  norm_num at this
  linarith

end LeanLab.Halupczok2012.Audit1614
#print axioms LeanLab.Halupczok2012.Audit1614.old_theorem_6_abstract_bounds_false
