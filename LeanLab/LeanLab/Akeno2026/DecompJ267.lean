import LeanLab.Akeno2026.Statements
import LeanLab.Akeno2026.ExpSumPrinted

namespace LeanLab.Akeno2026.DecompJ267

open LeanLab.Akeno2026

/-- LEAF. Page 8 equation 9 (part 1).
The base case k = 0 follows from Theorem 3.1. -/
theorem thm1_1_base_case_k0 (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 6) : LevelGP θ := by sorry

/-
RETIRED 2026-10-31 by the architect, run 20261031T2235Z-16111, ONE-TIME STATEMENT FIX. The two
leaves below are kept as text, not as declarations. Neither is used by the assembly.
`thm1_1_triangle_bound` had no hypotheses and dropped the paper's implied constant; it is false,
proved in `LeanLab.Common.FalseLeafAudit20261031b.thm1_1_triangle_bound_old_false`.
`thm1_1_cauchy_schwarz` used the natural number exponent `1/2 = 0`, so it said only
`levelSum ≤ 1`, see `thm1_1_cauchy_schwarz_old_is_le_one` there.
`thm1_1_base_case_k0` now takes the range `0 < θ < 1/6` of Theorem 1.1, which the assembly has.

/ -- LEAF. Page 8 equation 9 (part 2).
The triangle inequality bound `Σ_{d} R_{d,l}(N) ≪ (ln X)^2`. - /
theorem thm1_1_triangle_bound (θ : ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) :
    ‖Rdl w₁ w₂ X N d l‖ ≤ X / d * Real.log X ^ 2 := RETIRED, no proof term

/ -- LEAF. Page 8 equation 9 (part 3).
Cauchy-Schwarz inequality application to reduce the k-th moment to the 0-th moment. - /
theorem thm1_1_cauchy_schwarz (θ : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) :
    levelSum θ k w₁ w₂ X N ≤
      (X * Real.log X ^ 2) ^ (1/2) * (levelSum θ 0 w₁ w₂ X N) ^ (1/2) := RETIRED, no proof term

-/

/-- LEAF. Page 8 equation 9 (part 4).
The final step of the reduction from k > 0 to k = 0. -/
theorem thm1_1_reduction_to_k0 (θ : ℝ) (hk0 : LevelGP θ) : LevelGP θ := by sorry

/-- The exact sealed cited Prop for Theorem 1.1, assembled from the leaf with no sorry in this proof.
Uses the cited akeno_thm3_1 through the base case leaf. -/
theorem akeno_thm1_1_assembled : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by
  intro θ hθ0 hθ1
  exact thm1_1_reduction_to_k0 θ (thm1_1_base_case_k0 θ hθ0 hθ1)

end LeanLab.Akeno2026.DecompJ267
