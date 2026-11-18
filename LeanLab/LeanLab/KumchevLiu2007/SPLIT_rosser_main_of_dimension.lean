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

/-- LEAF: step one of the proof, the local product identity.  The strict
product below the close cutoff equals the product of the one minus local
factors taken over the distinct prime factors of the squarefree sieve product.
A prime outside the sieve support carries density zero, so its factor is one
on both sides and the two products agree.  This is an identity in the
definitions alone: it names no main sum, no level and no dimension estimate. -/
theorem strictProduct_eq_primeFactors_prod (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n =
      ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset, (1 - density n p) := by
  classical
  have hsupp : (primeProduct X δ n).primeFactorsList.dedup.toFinset = primeSupport X δ n := by
    have h1 : (primeProduct X δ n).primeFactorsList.dedup.toFinset =
        (primeProduct X δ n).primeFactors := by
      ext p
      simp
    rw [h1]
    unfold primeProduct
    have h2 := Nat.primeFactors_prod (s := primeSupport X δ n)
      (fun p hp => (Finset.mem_filter.mp hp).2.1)
    simpa using h2
  rw [hsupp]
  unfold strictProduct
  symm
  apply Finset.prod_subset
  · intro p hp
    unfold primeSupport at hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩, hp.2.2.1⟩
  · intro p hp hnot
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    have hd : ¬ 0 < density n p := fun h => hnot (by
      unfold primeSupport
      exact Finset.mem_filter.mpr ⟨hp.1.1, hp.1.2, hp.2, h⟩)
    have h0 : 0 ≤ density n p := by
      unfold density
      split_ifs <;> positivity
    have hz : density n p = 0 := le_antisymm (not_lt.mp hd) h0
    rw [hz, sub_zero]

/-- LEAF: step two of the proof, the weighted divisor to chain identity.  The
main sum of the explicit weights over the divisors of the sieve product equals
the alternating sum of prefix products over the distinct prime sublists, each
sublist carrying its own local factor at the product of the sublist.  This is
the weighted form of the squarefree divisor change of variables, so it is an
identity and it mentions no inequality, no constant and no level condition. -/
theorem mainSum_eq_chain_sum (X B δ ε D β : ℝ) (n : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).mainSum (rosserWeight D β)
      = ∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod := by
  sorry

/-- LEAF: step three of the proof, the chain main estimate.  For the dimension
constant it chooses a real exponent at least one, a positive constant and a
positive level exponent, and then the alternating chain sum of prefix products
over the distinct prime sublists is at most the constant times the product of
one minus the local factors, uniformly in the level, whenever the level
exponent dominates the cutoff, the cutoff is at least two, and the band
estimate for the inverse local product holds below the cutoff.  This is one
inequality about the chain sum: it carries no sieve model, no sequence, no B
and no upper divisor input. -/
theorem chain_sum_le_support_prod (K : ℝ) (hK : 2 ≤ K) :
    ∃ β C s : ℝ, 1 ≤ β ∧ 0 < C ∧ 0 < s ∧
      ∀ X δ D : ℝ, ∀ n : ℕ, ∀ hn : InH2 n,
        2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
        (Real.exp (Real.log X ^ (1 - δ / 2))) ^ s ≤ D →
        (∀ w v : ℝ, 2 ≤ w → w < v → v ≤ Real.exp (Real.log X ^ (1 - δ / 2)) →
          densityIntervalProduct n w v ≤ (Real.log v / Real.log w) ^ 2 *
            (1 + K / Real.log w)) →
        (∑ t ∈ (primeProduct X δ n).primeFactorsList.dedup.reverse.sublists.toFinset,
            (-1 : ℝ) ^ t.length * prefixRho D β t * density n t.prod) ≤
          C * ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset,
            (1 - density n p) := by
  sorry

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

#print axioms LeanLab.KumchevLiu2007.Task558b.strictProduct_eq_primeFactors_prod
