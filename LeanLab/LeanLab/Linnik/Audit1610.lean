/-
Unit U-1610, run 20261103T0803Z-22341. Instances for the plain expansion of `Decomp1532c`.
No refutation here: the old `major_arc_remainder_bound` was not false, its statement is unchanged.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp1532c

namespace LeanLab.Linnik.Audit1610

open LeanLab.Linnik.Decomp1532a (pairs dif)

/-- The hypotheses of `Display5PlainExpansion` can hold: `θ = 1/20`, `k = 2`, `δ = 1`, and the
sum over nonzero differences is not empty, `dif` being `-4` at the pair below for `L = 2`. -/
theorem display5_plain_instance :
    (0 : ℝ) < 1 / 20 ∧ 2 ≤ (2 : ℕ) ∧ (0 : ℝ) < 1 ∧ ∃ x : pairs 2 2, dif x ≠ 0 := by
  refine ⟨by norm_num, le_rfl, one_pos, (fun _ => 0, fun _ => 1), ?_⟩
  decide

end LeanLab.Linnik.Audit1610
