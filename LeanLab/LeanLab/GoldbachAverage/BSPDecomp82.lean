import LeanLab.GoldbachAverage.OmegaTransfer82

/-!
The large count input and integer omega assembly for P0050.
Source: arXiv 0806.3295v3 pages 4 and 5.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.BSPDecomp82

/-- LEAF. P0050 pages 4 and 5: G n is Omega of n log log n.
External input: Gallagher 1970, A Large Sieve Density Estimate near sigma equals one,
Theorem 7, with the exceptional character removed as described in P0050.
The paper derives the large count bound by averaging over multiples of a primorial. -/
theorem large_G : ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    c * N * Real.log (Real.log N) ≤ G N := by
  sorry

/-- The exact cited integer omega proposition, assembled from the large count leaf.
CONDITIONAL ON large_G. The assembly contains no sorry. -/
theorem bsp_omega_assembled : RiemannHypothesis → ¬ ErrSmallO := by
  intro hRH
  exact OmegaTransfer82.bsp_omega_of_large_values hRH large_G

example : type_of% bsp_omega := bsp_omega_assembled

end LeanLab.GoldbachAverage.BSPDecomp82
