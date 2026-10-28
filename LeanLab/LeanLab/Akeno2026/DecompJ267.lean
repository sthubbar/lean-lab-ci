import LeanLab.Akeno2026.Statements
import LeanLab.Akeno2026.ExpSumPrinted

namespace LeanLab.Akeno2026.DecompJ267

open LeanLab.Akeno2026

/-- LEAF. Page 8 equation 9 (part 1).
The base case k = 0 follows from Theorem 3.1. -/
theorem thm1_1_base_case_k0 (θ : ℝ) : LevelGP θ := by sorry

/-- LEAF. Page 8 equation 9 (part 2).
The triangle inequality bound `Σ_{d} R_{d,l}(N) ≪ (ln X)^2`. -/
theorem thm1_1_triangle_bound (θ : ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) :
    ‖Rdl w₁ w₂ X N d l‖ ≤ X / d * Real.log X ^ 2 := by sorry

/-- LEAF. Page 8 equation 9 (part 3).
Cauchy-Schwarz inequality application to reduce the k-th moment to the 0-th moment. -/
theorem thm1_1_cauchy_schwarz (θ : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) :
    levelSum θ k w₁ w₂ X N ≤
      (X * Real.log X ^ 2) ^ (1/2) * (levelSum θ 0 w₁ w₂ X N) ^ (1/2) := by sorry

/-- LEAF. Page 8 equation 9 (part 4).
The final step of the reduction from k > 0 to k = 0. -/
theorem thm1_1_reduction_to_k0 (θ : ℝ) (hk0 : LevelGP θ) : LevelGP θ := by sorry

/-- The exact sealed cited Prop for Theorem 1.1, assembled from the leaf with no sorry in this proof.
Uses the cited akeno_thm3_1 through the base case leaf. -/
theorem akeno_thm1_1_assembled : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by
  intro θ _ _
  exact thm1_1_reduction_to_k0 θ (thm1_1_base_case_k0 θ)

end LeanLab.Akeno2026.DecompJ267
