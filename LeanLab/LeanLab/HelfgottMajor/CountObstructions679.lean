import Mathlib

/-!
The unrestricted conductor premise in DecompF1619 is false at height one hundred.
The original sealed declaration stays unchanged.
This is a defect of the split premise, not a claim of an error in the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.CountObstructions679

/-- Negation of the universal closure of DecompF1619.log_q_le_point_one_t_sq.
At t equal to one hundred the right side is one thousand, while log q is unbounded. -/
theorem log_q_le_point_one_t_sq_false :
    ¬ ∀ (q : ℕ) [NeZero q] (t : ℝ), 100 ≤ t → Real.log (q : ℝ) ≤ 0.1 * t ^ 2 := by
  intro h
  obtain ⟨q, hq⟩ := exists_nat_gt (Real.exp 1000)
  have hqpos : (0 : ℝ) < q := (Real.exp_pos _).trans hq
  have hqn : 0 < q := by exact_mod_cast hqpos
  have hlog : (1000 : ℝ) < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt hqpos).mpr hq
  have hb := @h q ⟨Nat.ne_of_gt hqn⟩ 100 (by norm_num)
  norm_num at hb
  linarith

end LeanLab.HelfgottMajor.CountObstructions679

#print axioms LeanLab.HelfgottMajor.CountObstructions679.log_q_le_point_one_t_sq_false
