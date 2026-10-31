/-
AI wrote this Lean code for CODEX task58.
Discharge the remaining explicit exponential constant input for the lab c0 bracket.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Certified
import LeanLab.Helfgott2013.GammaFine

open Real Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact rational harmonic lower certificate needed for the named exponential input. -/
theorem harmonic4096_lower : (8895103896966 / 1000000000000 : ℚ) < harmonic 4096 := by
  decide +kernel

/-- A lower gamma bound sufficient for the original exponential bracket. -/
theorem gamma_lower_task58 : (0.577215656 : ℝ) < eulerMascheroniConstant := by
  have h := LeanLab.ChenExplicit.Gamma.u_le_gamma 4096 (by norm_num)
  unfold LeanLab.ChenExplicit.Gamma.u at h
  have hH : ((8895103896966 / 1000000000000 : ℚ) : ℝ) < (harmonic 4096 : ℝ) :=
    Rat.cast_lt.mpr harmonic4096_lower
  have hl := log_two_lt_d9
  have he : log ((4096 : ℕ) : ℝ) = 12 * log 2 := by
    rw [show ((4096 : ℕ) : ℝ) = 2 ^ 12 by norm_num, log_pow]
    norm_num
  rw [he] at h
  generalize ((harmonic 4096 : ℚ) : ℝ) = HH at h hH
  norm_num at h hH hl ⊢
  linarith

/-- The original exponential lower endpoint follows from twelve positive series terms. -/
theorem exp_gamma_lower_task58 : (1.7810724 : ℝ) < exp eulerMascheroniConstant := by
  have h1 : (1.7810724 : ℝ) ≤ exp (0.577215656 : ℝ) := by
    have h := sum_le_exp_of_nonneg (x := (0.577215656 : ℝ)) (by norm_num) 12
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  exact h1.trans_lt (exp_lt_exp.mpr gamma_lower_task58)

/-- The exact original exponential bracket, with no cited hypothesis. -/
theorem expGammaBracket_proved : U1435.ExpGammaBracket := by
  exact ⟨exp_gamma_lower_task58.le, LeanLab.Helfgott2013.GammaFine.exp_gamma_lt.le⟩

/-- The exact original c0 decimal bracket without either numerical hypothesis. -/
theorem c0_bracket_unconditional : (0.06140 : ℝ) ≤ U1435.c0 ∧ U1435.c0 ≤ 0.06141 :=
  c0_bracket_of_expGamma expGammaBracket_proved

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.harmonic4096_lower
#print axioms LeanLab.ChenPrimeExceptional.Task58.gamma_lower_task58
#print axioms LeanLab.ChenPrimeExceptional.Task58.exp_gamma_lower_task58
#print axioms LeanLab.ChenPrimeExceptional.Task58.expGammaBracket_proved
#print axioms LeanLab.ChenPrimeExceptional.Task58.c0_bracket_unconditional
