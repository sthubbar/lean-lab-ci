import Mathlib

/-!
A lower bound for arbitrary real zero data alone does not give display 1.10.
The missing zero density input cannot be replaced by that elementary bound alone.
This is a statement about abstract data, not a counterexample to Zhao's theorem.
Source: the lower bound in display 1.9 and the target in display 1.10, pages 2 and 3.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- Arbitrarily many equal real lambda values defeat a uniform square sum bound. -/
theorem lower_bound_alone_not_enough (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ n : ℕ, 1 < (∑ _j : Fin n, Real.exp (-(10 / 3 * c0))) ^ 2 := by
  have he : 0 < Real.exp (-(10 / 3 * c0)) := Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / Real.exp (-(10 / 3 * c0)))
  have hprod : 1 < (n : ℝ) * Real.exp (-(10 / 3 * c0)) := (div_lt_iff₀ he).mp hn
  refine ⟨n, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [sq_nonneg ((n : ℝ) * Real.exp (-(10 / 3 * c0)) - 1)]

#print axioms lower_bound_alone_not_enough

end LeanLab.Zhao2025.Task56
