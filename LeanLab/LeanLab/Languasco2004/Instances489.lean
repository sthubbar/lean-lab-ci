/-
Concrete domains for task489 source statements.
PP1993 pages 43 to 48, https://doi.org/10.1112/jlms/s2-47.1.41.
These are nonvacuity checks, not a computation range extension.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp489b
import LeanLab.Languasco2004.Decomp489c
import LeanLab.Languasco2004.Decomp489d

namespace LeanLab.Languasco2004.Instances489
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp489a Decomp489b Decomp489c Decomp489d
noncomputable section

/-- Pages 43 and 47 display 21: the principal character has coefficient minus one at n = 1. -/
theorem character_sum_instances :
    characterSum (1 : DirichletCharacter ℂ 1) 1 0 = -1 ∧
      shortCharacterSum (1 : DirichletCharacter ℂ 1) 1 0 1 = -1 := by
  norm_num [characterSum, shortCharacterSum, phase, Finset.sum_filter, Finset.filter_singleton]

/-- Page 47 display 18: the fixed modulus density endpoint has zero left side. -/
theorem fixed_modulus_endpoint {q : ℕ} [NeZero q] (T : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, Density279.zeroCount χ 1 T) = 0 := by
  simp [Density279.zeroCount_at_one]

/-- Page 47 display 16: at N = exp 1 the zero free rectangle reduces to real part 1. -/
theorem good_character_instance {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ ∈ goodCharacters q (Real.exp 1) 1 1 := by
  classical
  simp only [goodCharacters, dite_eq_right (NeZero.ne q), Finset.mem_filter, Finset.mem_univ, true_and]
  intro ρ hp hr _ _
  have hr1 : 1 ≤ ρ.re := by simpa only [Real.log_exp, Real.log_one, mul_zero, zero_div, sub_zero] using hr
  exact χ.LFunction_ne_zero_of_one_le_re hp hr1

/-- Pages 43 and 46: the punctured symmetric envelope is not empty. -/
theorem punctured_envelope_instance :
    (1 / 4 : ℝ) ∈ puncturedEnvelope (Real.exp 1) 100 16 1 1 := by
  norm_num [puncturedEnvelope, fareyOrder, Real.log_exp]

/-- Page 44 display 3: both squared weight sums vanish at unit length and position. -/
theorem weight_instances : firstWeight 1 1 = 0 ∧ secondWeight 1 = 0 := by
  norm_num [firstWeight, secondWeight]

/-- Page 48 display 26: all sigma and saving premises can hold together. -/
theorem logarithmic_instances :
    (1 / 2 : ℝ) ≤ 1 ∧
      (1 : ℝ) ≤ 1 - 2 * arcExponent 1 1 * Real.log (Real.log (Real.exp 1)) /
        Real.log (Real.exp 1) ∧
      localization (Real.exp 1) 1 ^ (1 - (1 : ℝ) / 3 * (1 - 1)) =
        localization (Real.exp 1) 1 / Real.log (Real.exp 1) ^ (2 * (1 : ℝ) + 23) := by
  norm_num [Real.log_exp]

/-- Page 47 display 20: the good character energy is nonnegative. -/
theorem goodEnergy_nonneg (q : ℕ) (N Y H B : ℝ) : 0 ≤ goodEnergy q N Y H B := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

#print axioms character_sum_instances
#print axioms fixed_modulus_endpoint
#print axioms good_character_instance
#print axioms punctured_envelope_instance
#print axioms weight_instances
#print axioms logarithmic_instances
#print axioms goodEnergy_nonneg
end
end LeanLab.Languasco2004.Instances489
