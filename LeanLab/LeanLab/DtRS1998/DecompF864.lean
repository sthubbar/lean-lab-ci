import LeanLab.DtRS1998.SPLIT_leaf_quarter_first_250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

def qsF864 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]

/-- LEAF Length bound for the first eighth covering list -/
theorem leaf_len_F864 : qsF864.length ≤ 15 := by sorry

/-- LEAF Primality of the first eighth covering list -/
theorem leaf_prime_F864 : ∀ q ∈ qsF864, q.Prime := by sorry

/-- LEAF Coverage for the first eighth index range -/
theorem leaf_cov_F864 : ∀ j : ℕ, j < 31250001 → qsF864.any (fun q => decide (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true := by sorry

theorem leaf_eighth_first_250_F864 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ j : ℕ, j < 31250001 → qs.any (fun q => decide (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  refine ⟨qsF864, ?_, ?_, ?_⟩
  · exact leaf_len_F864
  · exact leaf_prime_F864
  · exact leaf_cov_F864

end LeanLab.DtRS1998.Decomp270b
