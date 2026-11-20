import Mathlib
import LeanLab.BS2022GRH.ThetaInputs224

/-! AI wrote the Lean code. Goldbach is open.

Flag unit U-1735, run 20261120-flags2, folder BS2022GRH.

Part 1. Named hypothesis for Broadbent et al. Table 15 p. 32 row 37,
the exact sealed statement ThetaInputs224.theta_table15_37.
Part 2. A constant parametric family of the same row, with monotonicity in the
constant, so that a corrected published row with a larger constant can be
plugged in once a source copy is read.

Context: a Gemini outline reports that the printed proof of this row goes through
Buthe 2016 Theorem 1, whose constant E2 is said to miss a factor log of 3c.
That report is unverified here: no copy of Buthe 2016, of BKLNW, or of the
cited thesis is on disk. The row stays a cited input. -/

namespace LeanLab.BS2022GRH.Flag1735
open Real

/-- Theta row with constant c above exp 37. Plain math: for every x greater
than e to the 37, the absolute value of theta x minus x is at most c x over log x.
Source: Broadbent et al. Theorem 1 and Table 15 p. 32, row 37, at c 8.6315e-7. -/
def ThetaRow37 (c : ℝ) : Prop :=
  ∀ x : ℝ, exp 37 < x → |Chebyshev.theta x - x| ≤ c * x / log x

/-- Named hypothesis: the published row 37 with its printed constant. -/
def ThetaTable15Row37Flag : Prop := ThetaRow37 8.6315e-7

/-- Match theorem: the named hypothesis is the sealed statement of
ThetaInputs224.theta_table15_37, quantified over x. -/
theorem match_theta_table15_37 :
    ThetaTable15Row37Flag ↔
      ∀ x : ℝ, exp 37 < x →
        |Chebyshev.theta x - x| ≤ 8.6315e-7 * x / log x :=
  Iff.rfl

/-- A row with a smaller constant implies the row with any larger constant. -/
theorem row37_mono {c d : ℝ} (hcd : c ≤ d) (h : ThetaRow37 c) : ThetaRow37 d := by
  intro x hx
  have hx0 : 0 < x := lt_trans (exp_pos 37) hx
  have hlog : 0 < log x := by
    have : (1 : ℝ) < x := lt_trans (by
      have := add_one_lt_exp (by norm_num : (37 : ℝ) ≠ 0); linarith) hx
    exact log_pos this
  refine le_trans (h x hx) ?_
  apply div_le_div_of_nonneg_right _ hlog.le
  exact mul_le_mul_of_nonneg_right hcd hx0.le

/-- Weakening example: the printed row gives the row at constant 1e-6, which
covers the roughly 8.75e-7 to 8.82e-7 value the outline reports for a corrected
proof. CONDITIONAL on the named hypothesis. -/
theorem row37_weak_of_flag (h : ThetaTable15Row37Flag) : ThetaRow37 1e-6 :=
  row37_mono (by norm_num) h

end LeanLab.BS2022GRH.Flag1735
