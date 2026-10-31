/-
AI wrote this Lean code. CODEX task44.
BJS arXiv 2207.09452 v6, Theorem 44, page 42.
The printed u0 condition fails at the U1498 boundary with alpha equal 1e-5.
This is a parameter obstruction. It is no claim of a paper error.
-/
import LeanLab.ChenExplicit.U1490NuX1
import LeanLab.ChenExplicit.U1498MX3

open Real

noncomputable section
namespace LeanLab.ChenExplicit.PrintedRange31567

abbrev ll : ℝ := 31567 / 1000
abbrev LX : ℝ := exp ll
abbrev Lx : ℝ := LX - 5 * ll
abbrev alpha : ℝ := 1 / 100000
abbrev u0 : ℝ := 1000000000

/-- The logarithm of the left side of the printed Theorem 44 size condition at X2. -/
def logRatio : ℝ := LX * alpha - 10 * log Lx - 2.5 * log LX

/-- The logarithm of the right side of the printed Theorem 44 size condition. -/
def logRequired : ℝ := u0 * (1 + 9e-7 / log u0)

lemma logLx_nonneg : 0 ≤ log Lx := by
  have h := U1490NuX1.logLx_ge
  norm_num [U1490NuX1.Lx, Lx, LX, ll] at h ⊢
  linarith

lemma logLX_eq : log LX = ll := log_exp _

lemma logRatio_lt_u0 : logRatio < u0 := by
  have h : LX ≤ 8e13 := by
    have h := U1490NuX1.LX_le
    norm_num [U1490NuX1.LX, LX, ll] at h ⊢
    exact h
  have hx := logLx_nonneg
  unfold logRatio
  rw [logLX_eq]
  norm_num [alpha, u0, ll] at *
  linarith

lemma u0_le_logRequired : u0 ≤ logRequired := by
  have h : 0 ≤ 9e-7 / log u0 := div_nonneg (by norm_num) (log_nonneg (by norm_num))
  unfold logRequired
  have : 0 ≤ u0 := by norm_num
  nlinarith

/-- The printed condition cannot be discharged at the U1498 boundary with its alpha. -/
theorem printed_u0_condition_fails : exp logRatio < exp logRequired := by
  exact exp_lt_exp.mpr (logRatio_lt_u0.trans_le u0_le_logRequired)

/-- Concrete instance of the failed logarithmic inequality. -/
example : ¬ logRequired ≤ logRatio := not_le.mpr (logRatio_lt_u0.trans_le u0_le_logRequired)

#print axioms logLx_nonneg
#print axioms logLX_eq
#print axioms logRatio_lt_u0
#print axioms u0_le_logRequired
#print axioms printed_u0_condition_fails

end LeanLab.ChenExplicit.PrintedRange31567
