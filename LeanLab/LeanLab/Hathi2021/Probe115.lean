import LeanLab.Hathi2021.Decomp115

open Finset Real

namespace LeanLab.Hathi2021.Decomp115

-- scratch probe for the analytic_lower_bound goal, FREE-nv-glm task26
example (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (PairLinnik.margin101 (108238 / 10) 82 - ε) *
        ((n₁ : ℝ) * n₂ * logScale n₁ ^ 82) ≤ weightedCount n₁ n₂ := by
  exact?

end LeanLab.Hathi2021.Decomp115
