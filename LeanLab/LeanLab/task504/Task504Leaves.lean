import LeanLab.ChenDoubleSieve.Decomp347j

/-!
The repair record for the branch free-ms-leanstral/task504.
Source: https://arxiv.org/pdf/0705.1652, page 35 Upsilon 10 and page 36 S1 crossing split.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task504
open Task347
open Task275 Task315

/-- Membership in the lower crossing band without evaluating its ambient finite cube.
Source: page 36 second display before the split at rho, derived domain characterization. -/
private theorem mem_lowerCrossingPairs {N p q : ℕ} :
    (p, q) ∈ lowerCrossingPairs N ↔ p < N ∧ q < N ∧ p.Prime ∧ q.Prime ∧
      p.Coprime N ∧ q.Coprime N ∧ (N : ℝ) ^ kappa1 ≤ p ∧
      (p : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ q ∧
      (q : ℝ) < (N : ℝ) ^ sigma2 := by
  simp only [lowerCrossingPairs, Wu08Sum.P2, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The Upsilon 10 crossing domain and the lower S1 crossing band are disjoint: a pair in the
first has second coordinate at least `N ^ sigma2`, a pair in the second has it strictly below
that number. So no crossing pair is ever counted by the lower crossing sum.
Source: page 35 definition of Upsilon 10 and page 36 S1 crossing split at rho. -/
theorem crossingPairs_disjoint_lowerCrossingPairs (N : ℕ) :
    Disjoint (crossingPairs N) (lowerCrossingPairs N) := by
  rw [Finset.disjoint_left]
  rintro ⟨p, q⟩ h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, hge, _⟩ := mem_crossingPairs.mp h1
  obtain ⟨_, _, _, _, _, _, _, _, _, hlt⟩ := mem_lowerCrossingPairs.mp h2
  exact (not_le_of_gt hlt) hge

end LeanLab.ChenDoubleSieve.Task504
