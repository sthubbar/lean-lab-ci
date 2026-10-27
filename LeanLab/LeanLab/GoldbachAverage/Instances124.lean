import LeanLab.GoldbachAverage.Decomp124
import LeanLab.GoldbachAverage.Decomp124b

/-!
Concrete range checks for the prime count in P0098 Theorem 2 and Proposition 3.1.
These checks do not assert the uniform Goldbach count hypothesis.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Instances124
open Decomp124 Finset Set

/-- The prime-only count has one ordered representation at four, namely two plus two.
Source: P0098 page 159 definition of g. -/
theorem primePairs_four : primePairs 4 = 1 := by
  norm_num [primePairs, Finset.range_add_one, Finset.filter_insert]

/-- A nonvacuous member of N gamma at gamma equal to one hundredth.
Source: P0098 page 165 Proposition 3.1. -/
theorem rich_four : 4 ∈ richEven ((1 : ℝ) / 100) := by
  refine ⟨by decide, by norm_num, ?_⟩
  rw [primePairs_four]
  have hlog : 1 ≤ Real.log (4 : ℝ) := by
    have := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  norm_num only [Nat.cast_ofNat]
  rw [div_lt_iff₀ (by positivity : 0 < Real.log (4 : ℝ) ^ 2)]
  nlinarith [sq_nonneg (Real.log (4 : ℝ) - 1)]

/-- The empty sample has zero count at every real endpoint.
Source: P0098 page 167 definition of P x. -/
theorem count_empty (x : ℝ) : count ∅ x = 0 := by simp [count]

/-- Choosing no selector yields the empty prime subset.
Source: P0098 page 166 definition of the prime selection process. -/
theorem coinSet_false : coinSet (fun _ => false) = ∅ := by
  ext p
  simp [coinSet]

/-- The empty prime sample misses exactly four at the first nontrivial cutoff.
Source: the exception count in P0098 Theorem 3, page 163. -/
theorem badEven_empty_four : State124.badEven ∅ 4 = 1 := by
  norm_num [State124.badEven, Finset.range_add_one, Finset.filter_insert]

/-- No poor even lies in the Goldbach range below four.
Source: P0098 page 167 exception split. -/
theorem poorEven_two (γ : ℝ) : Decomp124b.poorEven γ 2 = 0 := by
  norm_num [Decomp124b.poorEven, Finset.range_add_one, Finset.filter_insert]

/-- No rich even lies in the Goldbach range below four.
Source: P0098 page 167 exception split. -/
theorem missedRich_two (P : Set ℕ) (γ : ℝ) : Decomp124b.missedRich P γ 2 = 0 := by
  norm_num [Decomp124b.missedRich, richEven, Finset.range_add_one, Finset.filter_insert]

end LeanLab.GoldbachAverage.Instances124
