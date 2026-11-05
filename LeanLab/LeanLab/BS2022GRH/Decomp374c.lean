/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Reuse the existing three range Mertens development for the older interval leaf.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.DecompC169c

namespace LeanLab.BS2022GRH.Decomp374c
open Real Finset Classical ChenThresholdGRH Decomp138

/-- Exact statement of Decomp138.reciprocal_sum_lt, journal p. 1222 display 9.
The proof already exists as the task138 finite bridge and task224 one sided inputs.
CONDITIONAL ON the existing numerical theta and finite computation leaves. -/
theorem reciprocal_sum_lt (z u : ℝ) (hz : exp 2753 < z) (hu : 400 ≤ u) (huz : u < z) :
    ∑ p ∈ band u z, (1 : ℝ) / p < log (log z) - log (log u) + 1.131e-7 := by
  exact Mertens138.reciprocal_sum_lt_of_mertens z u DecompC169c.mertensConstant hz hu huz
    (Lemma6Input138.upper_strict_below _ DecompC169c.lemma6J z hz)
    (Lemma6Input138.lower_uniform _ DecompC169c.lemma6J u hu)

end LeanLab.BS2022GRH.Decomp374c

#print axioms LeanLab.BS2022GRH.Decomp374c.reciprocal_sum_lt
