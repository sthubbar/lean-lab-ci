import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
A scalar audit of the untrusted outline supplied for P0014 display 4.26.
This tests the outline budget only. It makes no claim about the paper or Gamma error.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.OutlineAudit433
open Real

/-- The outline Stirling budget at parity 1 and height 1 exceeds its claimed 0.35.
The source role is an audit of the outline for P0014 page 38, display 4.26.
The paper cites the count theorem and does not assert this scalar budget.
-/
theorem outline_stirling_budget_gt :
    (0.35 : ℝ) <
      1 / (2 * π) * log (1 + (1 / 2 + 1 : ℝ) ^ 2) +
        (1 / 2 + 1 : ℝ) / π +
        1 / (12 * π * ‖(3 / 4 : ℂ) + (1 / 2 : ℂ) * Complex.I‖) := by
  have hl : 0 ≤ log (1 + (1 / 2 + 1 : ℝ) ^ 2) := log_nonneg (by norm_num)
  have hp : (0.375 : ℝ) < (1 / 2 + 1 : ℝ) / π := by
    rw [lt_div_iff₀ pi_pos]
    nlinarith [pi_lt_four]
  have ha : 0 ≤ 1 / (2 * π) * log (1 + (1 / 2 + 1 : ℝ) ^ 2) := by positivity
  have hb : 0 ≤ 1 / (12 * π * ‖(3 / 4 : ℂ) + (1 / 2 : ℂ) * Complex.I‖) := by positivity
  linarith

end LeanLab.HelfgottMajor.OutlineAudit433
