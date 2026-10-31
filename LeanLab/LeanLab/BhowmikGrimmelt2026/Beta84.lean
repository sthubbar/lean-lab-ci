/-
The beta factor limit used at the start of Section 8, page 30.
The complex limit implies the real limit stated for an exceptional zero.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Page 30, before display 8.1. The beta factor tends to one at the unit arguments. -/
theorem betaC_tendsto_one84 :
    Tendsto (fun β : ℂ => betaC β β) (𝓝 1) (𝓝 1) := by
  have hΓ2 : Complex.Gamma (2 : ℂ) = 1 := by
    simpa using Complex.Gamma_nat_eq_factorial 1
  have h2 : ContinuousAt Complex.Gamma (2 : ℂ) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have hr : (2 : ℝ) = -(n : ℝ) := by simpa using congrArg Complex.re hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpoint : ContinuousAt Complex.Gamma ((1 : ℂ) + 1) := by
    convert h2 using 1 <;> norm_num
  have hden : ContinuousAt (fun β : ℂ => Complex.Gamma (β + β)) 1 :=
    hpoint.comp (f := fun β : ℂ => β + β)
      (continuous_id.continuousAt.add continuous_id.continuousAt)
  have hcont : ContinuousAt (fun β : ℂ => betaC β β) 1 := by
    unfold betaC
    exact (Complex.continuousAt_Gamma_one.mul Complex.continuousAt_Gamma_one).div
      hden (by norm_num [hΓ2])
  have hb : betaC (1 : ℂ) 1 = 1 := by norm_num [betaC, hΓ2]
  simpa only [hb] using hcont.tendsto

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.betaC_tendsto_one84
