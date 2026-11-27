/- AI wrote this Lean code for CODEX task700. Goldbach is open.
Continuity used in the existing fixed kappa limiting step.
BJS arXiv 2207.09452v6 display 7 and the sieve limiting argument.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Thm6Factor

namespace LeanLab.BS2022GRH.Limit700
open Real Filter Topology Set
noncomputable section

/-- A continuous formula for the three pieces of the paper's envelope. -/
theorem hS_eq_max (s : ℝ) : hS s = 3 / max s 3 * exp (-max s 2) := by
  by_cases h2 : s ≤ 2
  · simp [hS, h2, max_eq_right (by linarith : s ≤ 3)]
  · by_cases h3 : s ≤ 3
    · simp [hS, h2, h3, max_eq_left (le_of_not_ge h2)]
    · simp [hS, h2, h3, max_eq_left (le_of_not_ge h2),
        max_eq_left (le_of_not_ge h3)]

/-- The envelope is continuous, including both junctions. -/
theorem continuous_hS : Continuous hS := by
  simp_rw [funext hS_eq_max]
  apply Continuous.mul
  · exact continuous_const.div (continuous_id.max continuous_const)
      (fun s => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_right s 3)))
  · fun_prop

end
end LeanLab.BS2022GRH.Limit700

#print axioms LeanLab.BS2022GRH.Limit700.hS_eq_max
#print axioms LeanLab.BS2022GRH.Limit700.continuous_hS
