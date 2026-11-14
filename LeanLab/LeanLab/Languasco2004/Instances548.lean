/-
Concrete parameter and integrand instances for the task548 source statements.
Jia 1996 pages 267 to 286.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are required domain checks, not a range extension computation.
-/
import LeanLab.Languasco2004.GroupSplit548
import LeanLab.Languasco2004.MovingIntegral548
import LeanLab.Languasco2004.Instances316
import LeanLab.Languasco2004.Kernel548

namespace LeanLab.Languasco2004.Instances548
open Real Set Finset intervalIntegral GroupSplit548 MovingIntegral548 Kernel548
open Decomp279a BuchstabInitial316
noncomputable section

/-- Pages 275 and 281: the selected source region domains admit exact rational points. -/
theorem source_domain_instances :
    11 / 27 ≤ (11 / 27 : ℝ) ∧ (11 / 27 : ℝ) ≤ 34 / 81 ∧
    17 / 12 - 23 / 8 * (11 / 27 : ℝ) ≤ 53 / 216 ∧
    (53 / 216 : ℝ) ≤ 25 / 72 - (11 / 27 : ℝ) / 4 ∧
    34 / 99 ≤ (34 / 99 : ℝ) ∧ (34 / 99 : ℝ) ≤ 1649 / 4752 ∧
    85 / 99 - 2 * (34 / 99 : ℝ) ≤ 17 / 99 ∧
    (17 / 99 : ℝ) ≤ 85 / 147 - 58 / 49 * (34 / 99 : ℝ) := by
  norm_num

/-- Pages 270 and 275: the common endpoint of the explicit formulas gives a nonzero kernel. -/
theorem kernel_endpoint_instance :
    buchstabInitial ((1 - (1 / 4 : ℝ) - 1 / 4) / (1 / 4)) /
      ((1 / 4 : ℝ) * (1 / 4)^2) = 32 := by
  norm_num [buchstabInitial]

/-- Pages 267 to 269: either piece vanishes under an empty finite cap. -/
theorem empty_piece_instances (j i : ℕ) :
    pieceSum j i true 2 2 0 = 0 ∧ pieceSum j i false 2 2 0 = 0 :=
  ⟨pieceSum_empty j i true 2 2, pieceSum_empty j i false 2 2⟩

/-- Page 208 and Lemmas 24 to 28: the positive small parameter and localization domain are inhabited. -/
theorem parameter_domain_instance :
    (0 : ℝ) < 1 / 2000 ∧ (1 / 2000 : ℝ) < 1 / 100 ∧ (0 : ℝ) < 1 ∧
      1 < localization 64 (1 / 2000) := by
  exact ⟨by norm_num, by norm_num, by norm_num, Instances316.localization_instance.1⟩

/-- Page 281 numerical support: the moving integral theorem has a nonzero constant kernel model. -/
theorem moving_integral_instance :
    ContinuousOn (fun _t : ℝ => ∫ _u in (0 : ℝ)..1, (1 : ℝ)) (Icc 0 1) ∧
      (∫ _u in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
  constructor
  · apply moving_integral_continuousOn (fun _ _ : ℝ => (1 : ℝ)) 0 1 0 1
      (fun _ => 0) (fun _ => 1) (by norm_num) (by norm_num)
      (by fun_prop) (by fun_prop) (by fun_prop)
    intro t ht
    norm_num
  · norm_num

#print axioms source_domain_instances
#print axioms kernel_endpoint_instance
#print axioms empty_piece_instances
#print axioms parameter_domain_instance
#print axioms moving_integral_instance
end
end LeanLab.Languasco2004.Instances548
