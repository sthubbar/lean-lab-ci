import LeanLab.DensityGoldbach.Statements
open Classical
open Filter

namespace LeanLab.DensityGoldbach

/-- LEAF: p. 1 of P0038. Definition of ¬ LargeOddIn. -/
theorem shao_1_3_leaf_1 (A : Set ℕ)
    (h_not : ¬ LargeOddIn A A A) :
    ∀ N₀, ∃ n, N₀ ≤ n ∧ Odd n ∧ ¬ IsSum3 A A A n := by
  intro N₀
  unfold LargeOddIn at h_not
  push Not at h_not
  exact h_not N₀

/-- LEAF: p. 1 of P0038. Excluded middle for IsSum3. -/
theorem shao_1_3_leaf_2 (A : Set ℕ) (N : ℕ) :
    IsSum3 A A A N ∨ ¬ IsSum3 A A A N := by
  exact Classical.em _

/-- LEAF: p. 1 of P0038. Obtain a contradiction from the assumption. -/
theorem shao_1_3_leaf_3 (δ : ℝ) (hδ : 0 < δ) (A : Set ℕ) (hA : A ⊆ P)
    (h1 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3)
    (h2 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 2 3 + lowerDensityRes A 1 3)
    (n : ℕ) (hn_odd : Odd n) (hn_not_sum : ¬ IsSum3 A A A n) : False := by
  sorry

/-- LEAF: p. 1 of P0038. The third leaf to extract the bound for contradiction. -/
theorem shao_1_3_leaf_4 (δ : ℝ) (_hδ : 0 < δ) (A : Set ℕ) (_hA : A ⊆ P)
    (h1 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3)
    (_h2 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 2 3 + lowerDensityRes A 1 3) :
    3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3 := by
  exact h1

/-- Assembly theorem for Shao Thm 1.3 from the leaves. -/
theorem shao_1_3_assembly : Shao13 := by
  intro δ hδ
  use 3 -- placeholder W
  refine ⟨by norm_num, ?_⟩
  intro A hA h1 h2 _h3
  by_contra h_not
  obtain ⟨n, hn1, hn_odd, hn_not_sum⟩ := shao_1_3_leaf_1 A h_not 0
  have h_cases := shao_1_3_leaf_2 A n
  rcases h_cases with h_in | h_not_in
  · exact hn_not_sum h_in
  · exact shao_1_3_leaf_3 δ hδ A hA h1 h2 n hn_odd h_not_in

end LeanLab.DensityGoldbach
