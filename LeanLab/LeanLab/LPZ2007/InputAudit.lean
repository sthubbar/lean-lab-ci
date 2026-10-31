/-
P0045, journal page 778, display 26 and its quoted numerical bound.
The lab coarse Romanov constant does not certify the quoted small numerical constant.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.Lemma61Port

namespace LeanLab.LPZ2007.InputAudit

open Real

/-- The currently available coarse Romanov constant exceeds 1.9378. -/
theorem coarse_romanov_bound_too_large : (1.9378 : ℝ) < 8 * log 2 * exp 27 := by
  have hl : (0.6 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have he : (28 : ℝ) ≤ exp 27 := by linarith [Real.add_one_le_exp (27 : ℝ)]
  calc (1.9378 : ℝ) < 8 * (0.6 : ℝ) * 28 := by norm_num
    _ ≤ 8 * log 2 * exp 27 := by gcongr

/-- Divisibility of the conductor of a square alone gives no modulus classification. -/
theorem power_conductor_condition_insufficient :
    (1 ∣ (2 : ℕ)) ∧ ¬ (2 = oddRad 2 ∨ 2 = 4 * oddRad 2 ∨ 2 = 8 * oddRad 2) := by
  have hrad : oddRad 2 = 1 := by norm_num [oddRad]
  simp [hrad]

end LeanLab.LPZ2007.InputAudit

#print axioms LeanLab.LPZ2007.InputAudit.coarse_romanov_bound_too_large

#print axioms LeanLab.LPZ2007.InputAudit.power_conductor_condition_insufficient
