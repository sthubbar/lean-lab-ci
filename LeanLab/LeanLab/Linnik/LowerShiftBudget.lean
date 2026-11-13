import Mathlib

namespace LeanLab.Linnik.Decomp1532c

/-- Gallagher 1975 p.127 Theorem 3 and p.138 display 5 retain an exponential error.
For a fixed theta and positive coefficient, some positive delta makes the
twenty-seventh budget smaller than that error at every positive main size.
This is an obstruction to absorbing the printed bound, not a counterexample to a leaf.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem lower_shift_fixed_exponential_budget_obstruction (c C θ : ℝ) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℝ, 0 < B →
      B * (δ / 27) < B * (C * Real.exp (-c / θ)) := by
  refine ⟨27 * (C * Real.exp (-c / θ)) / 2, by positivity, ?_⟩
  intro B hB
  apply mul_lt_mul_of_pos_left _ hB
  have hpos : 0 < C * Real.exp (-c / θ) := mul_pos hC (Real.exp_pos _)
  linarith

/-- A signed whole sum need not control a signed subsum.
The checked witness has values one and minus one on the two element set.
This refutes a proposed restriction step, not any of the three leaf statements.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem lower_shift_signed_subsum_not_monotone :
    ¬ ∀ (s : Finset ℕ) (g : ℕ → ℝ) (t : Finset ℕ), t ⊆ s →
      |∑ x ∈ t, g x| ≤ |∑ x ∈ s, g x| := by
  intro h
  have hb := h {0, 1} (fun n => if n = 0 then 1 else -1) {0} (by simp)
  norm_num at hb

end LeanLab.Linnik.Decomp1532c

#print axioms LeanLab.Linnik.Decomp1532c.lower_shift_fixed_exponential_budget_obstruction
#print axioms LeanLab.Linnik.Decomp1532c.lower_shift_signed_subsum_not_monotone
