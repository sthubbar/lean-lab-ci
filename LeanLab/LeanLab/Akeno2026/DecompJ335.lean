import LeanLab.Akeno2026.Prop44Inputs

namespace LeanLab.Akeno2026

open Real Set MeasureTheory intervalIntegral

/-- LEAF. Theorem 1.1 follows from Theorem 3.1. Page 7 of arXiv 2606.29559.
"For the proof of Theorem 1.1, we may just use Theorem 3.1 with β = Λ..." -/
theorem akeno_thm1_1_of_thm3_1
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η) :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by
  sorry

/-- The exact sealed cited Prop, assembled from named leaves with no sorry in this proof.
CONDITIONAL ON the cited analytic leaf `akeno_thm1_1_of_thm3_1`. -/
theorem akeno_thm1_1_assembled : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by
  exact akeno_thm1_1_of_thm3_1 akeno_thm3_1

end LeanLab.Akeno2026
