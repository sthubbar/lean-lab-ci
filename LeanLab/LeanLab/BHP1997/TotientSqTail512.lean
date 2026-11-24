/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, citing Vaughan 1981, chapter 3, book page 34, display 3.23.
Elementary bound on the tail of the sum of φ(r)^{-2}.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Section2MS
open Classical

/-- LEAF: Vaughan 1981 chapter 3, book page 34, the elementary fact printed under display
3.23: Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}, which
gives the bound min(Z^{-1}, 1) for every Z > 0, uniformly in the upper cutoff R.
Class MEDIUM: from Σ_{q≤R} (q/φ(q))² ≪ R, which follows from
q/φ(q) = Σ_{d|q} μ(d)²/φ(d), and partial summation. -/
theorem leaf_totient_sq_tail512_leaf :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 := by
  sorry

end LeanLab.BHP1997.Section2MS
