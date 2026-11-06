/-
Concrete domains and arithmetic data for the task413 source twins.
AI wrote the Lean code. Goldbach is open.
These are vacuity checks, not a computation range extension.
-/
import LeanLab.Languasco2004.PPAssembly413
import LeanLab.Languasco2004.KernelSupport413
import LeanLab.Languasco2004.RationalPartition413

namespace LeanLab.Languasco2004.Instances413
open Finset Real MeasureTheory Decomp279b Decomp413b RationalPartition413
noncomputable section
attribute [local instance] Classical.propDecidable

/-- PP1993 pages 43 and 45 display 7: the two principal geometric sums
and rational coefficient take the predicted values at their smallest index. -/
theorem principal_data_instances :
    firstModel 1 1 0 = 1 ∧ secondModel 1 0 = 1 ∧ rationalWeight 1 = 1 ∧
      firstRemainder 1 1 1 1 0 = -1 ∧ secondRemainder 1 1 1 0 = -1 := by
  norm_num [firstModel, secondModel, rationalWeight, firstRemainder, secondRemainder,
    firstSum, secondSum, phase]

/-- PP1993 page 45 display 7: zero data give a zero rational integral. -/
theorem rationalIntegral_zero (N Y H B : ℝ) (m : ℕ) :
    rationalIntegral N Y H B m (fun _ _ _ => 0) = 0 := by
  simp [rationalIntegral]

/-- PP1993 page 45 display 7: a concrete positive source domain satisfies
the explicit arc separation bound used in the geometric assembly. -/
theorem major_geometric_instance (m : ℕ) :
    majorCoefficient (Real.exp 1) 100 16 1 m =
      principalCoefficient (Real.exp 1) 100 16 1 m +
      remainderCoefficient (Real.exp 1) 100 16 1 m := by
  rw [major_to_rational (Real.exp 1) 100 16 1 m
    (by exact Real.one_lt_exp_iff.mpr (by norm_num)) (by norm_num)
    (by norm_num [Real.log_exp])]
  exact rational_product_decomposition _ _ _ _ _

/-- PP1993 page 45 display 7: the sample major domain is nonempty.
The reduced centre one lies strictly inside its positive rational arc. -/
theorem major_domain_nonempty_instance :
    (1 : ℝ) ∈ period 16 ∩ majorSet (Real.exp 1) 100 1 := by
  refine ⟨?_, ?_⟩
  · norm_num [period]
  · refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num, by decide, ?_⟩ <;>
      norm_num [Real.log_exp]

#print axioms principal_data_instances
#print axioms rationalIntegral_zero
#print axioms major_geometric_instance
#print axioms major_domain_nonempty_instance
end
end LeanLab.Languasco2004.Instances413
