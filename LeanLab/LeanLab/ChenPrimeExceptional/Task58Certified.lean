/-
AI wrote this Lean code for CODEX task58.
The original IntegralBrackets hypothesis is now a theorem.
The analytic sieve identification on P0039 pages 66 to 67 remains a separate source question.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58IB1Bracket
import LeanLab.ChenPrimeExceptional.Task58NestedBrackets
import LeanLab.ChenPrimeExceptional.Task58J1Monotone

open Real Set intervalIntegral MeasureTheory

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The exact original six bounds, with no numerical or analytic input. -/
theorem integralBrackets_proved : U1435.IntegralBrackets := by
  obtain ⟨h1, h2⟩ := J1_bracket_unconditional
  obtain ⟨h3, h4⟩ := J2_bracket_unconditional
  obtain ⟨h5, h6⟩ := IB1_bracket_unconditional
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The original K bracket without IntegralBrackets as a hypothesis. -/
theorem K_bracket_unconditional : (0.017237 : ℝ) ≤ U1435.K ∧ U1435.K ≤ 0.017239 :=
  U1435.K_bracket integralBrackets_proved

/-- The original c0 bracket now needs only the separately named exponential constant bound. -/
theorem c0_bracket_of_expGamma (hg : U1435.ExpGammaBracket) :
    (0.06140 : ℝ) ≤ U1435.c0 ∧ U1435.c0 ≤ 0.06141 :=
  U1435.c0_bracket integralBrackets_proved hg

/-- Explicit decreasing endpoint rectangles on every J2 subinterval. -/
theorem j2_subinterval {a b : ℝ} (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 5)) (hab : a ≤ b) :
    (b - a) * j2Kernel b ≤ ∫ t in a..b, j2Kernel t ∧
      (∫ t in a..b, j2Kernel t) ≤ (b - a) * j2Kernel a := by
  apply antitone_cell hab
  · apply ContinuousOn.intervalIntegrable
    exact j2Kernel_continuous.mono (uIcc_subset_Icc ha hb)
  · exact j2Kernel_antitone.mono (Icc_subset_Icc ha.1 hb.2)

/-- Explicit decreasing endpoint rectangles on every B1 density subinterval. -/
theorem density_subinterval {a b : ℝ} (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 3))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 3)) (hab : a ≤ b) :
    (b - a) * density b ≤ ∫ t in a..b, density t ∧
      (∫ t in a..b, density t) ≤ (b - a) * density a := by
  apply antitone_cell hab
  · apply ContinuousOn.intervalIntegrable
    exact density_continuous.mono (uIcc_subset_Icc ha hb)
  · exact density_antitone.mono (Icc_subset_Icc ha.1 hb.2)

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.integralBrackets_proved
#print axioms LeanLab.ChenPrimeExceptional.Task58.K_bracket_unconditional
#print axioms LeanLab.ChenPrimeExceptional.Task58.c0_bracket_of_expGamma
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2_subinterval
#print axioms LeanLab.ChenPrimeExceptional.Task58.density_subinterval
#print axioms LeanLab.ChenPrimeExceptional.Task58.c0_pos_unconditional
#print axioms LeanLab.ChenPrimeExceptional.Task58.K_no35_neg_unconditional
