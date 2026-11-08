/-
Unit U-1625, run 20261106T0803Z-25677. Instances for the decision on `major_arc_remainder_bound`.
No refutation here: `display5_plain_expansion` is retired because it is stronger than the source
and not needed, not because it is false.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp1532c

namespace LeanLab.Linnik.Audit1625

open LeanLab.Linnik.Decomp1532a (pairs dif)

/-- The hypotheses of `major_arc_remainder_bound` can hold and its sum is not empty: `θ = 1/20`,
`k = 2`, `δ = 1`, `L = 2`, and `dif` is nonzero at the pair below. The exponential term of
Gallagher p.127 and p.138 is positive there. -/
theorem major_arc_remainder_instance :
    (0 : ℝ) < 1 / 20 ∧ 2 ≤ (2 : ℕ) ∧ (0 : ℝ) < 1 ∧ 0 < Real.exp (-1 / (1 / 20)) ∧
      ∃ x : pairs 2 2, dif x ≠ 0 := by
  refine ⟨by norm_num, le_rfl, one_pos, Real.exp_pos _, (fun _ => 0, fun _ => 1), ?_⟩
  decide

/-- With `C > 0` and positive main size the leaf allows strictly more error than the retired
plain form, which is the form with `C = 0`. -/
theorem source_allowance_gt_plain {M C c θ δ : ℝ} (hM : 0 < M) (hC : 0 < C) :
    M * δ < M * (C * Real.exp (-c / θ) + δ) := by
  have h := mul_pos hM (mul_pos hC (Real.exp_pos (-c / θ)))
  nlinarith

end LeanLab.Linnik.Audit1625

#print axioms LeanLab.Linnik.Audit1625.major_arc_remainder_instance
#print axioms LeanLab.Linnik.Audit1625.source_allowance_gt_plain
