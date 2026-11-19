/-
Split of the Rosser main sum dimension estimate of Decomp558b.
The target is carved into two exact identities on the coefficient sum and one
main estimate on the prime chain sum.  The identities transport the divisor sum
of the model into an alternating sum of prefix products, and transport the
product over the prime factors of the sieve product into the strict product.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp558b

namespace LeanLab.KumchevLiu2007.Task558b

open Real Task506b Task506d Task506e Task558a
open scoped BigOperators Topology

/-- The sealed target statement, assembled from the three leaves with no
admission and without the target theorem.  The existential parameters and the
constant come from the chain estimate.  The weighted divisor to chain identity
rewrites the main sum into the chain sum, and the local product identity
rewrites the chain bound into the strict product bound. -/
theorem rosser_main_of_dimension_split (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X B δ ε : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ Y X ε ^ (1 / 9 : ℝ) →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β) ≤
          C * strictProduct X δ n := by
  obtain ⟨β, C, s, hβ, hC, hs, hcore⟩ := chain_sum_le_support_prod K hK
  refine ⟨β, C, s, hβ, hC, hs, ?_⟩
  intro X B δ ε n hn hz hlev hband
  calc
    (sieveModel X B δ ε n hn).mainSum (rosserWeight (Y X ε ^ (1 / 9 : ℝ)) β)
        = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
              (-1 : ℝ) ^ t.length * prefixRho (Y X ε ^ (1 / 9 : ℝ)) β t *
                density n t.prod :=
          mainSum_eq_chain_sum X B δ ε (Y X ε ^ (1 / 9 : ℝ)) β n hn
    _ ≤ C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
          (1 - density n p) :=
          hcore X δ (Y X ε ^ (1 / 9 : ℝ)) n hn hz hlev hband
    _ = C * strictProduct X δ n := by rw [strictProduct_eq_primeFactors_prod]

end LeanLab.KumchevLiu2007.Task558b
