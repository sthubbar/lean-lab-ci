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

/- ===== private helpers (WIP pass 2026-11-17) ===== -/

/-- The local factor product over the sieve support.  The split's leaf one
ranges over `(primeProduct X δ n).primeFactorsList.dedup.toFinset`, which is
that support; a support prime carries positive density and every strict-cutoff
prime outside it carries density zero, so the two products agree. -/
private theorem strictProduct_eq_prod_primeSupport (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n = ∏ p ∈ primeSupport X δ n, (1 - density n p) := by
  classical
  unfold strictProduct primeSupport
  symm
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    obtain ⟨hmem, hprime, hpz, hpos⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, hprime⟩, hpz⟩
  · intro p hp hnot
    obtain ⟨hpT, hpz⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := (Finset.mem_filter.mp hpT).2
    have hzero : density n p = 0 := by
      have hnp : ¬ (0 < density n p) := fun hpos =>
        hnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, hprime, hpz, hpos⟩)
      linarith [density_nonneg n p]
    rw [hzero, sub_zero]

/-- The prime factor set of the sifting product is the sieve support. -/
private theorem primeFactors_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactors = primeSupport X δ n := by
  classical
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    exact prime_mem_of_dvd_product X δ n p hp hdvd
  · intro hp
    refine ⟨(Finset.mem_filter.mp hp).2.1, Finset.dvd_prod_of_mem _ hp, ?_⟩
    exact (primeProduct_squarefree X δ n).ne_zero

/-- The distinct prime factors of the sifting product, as a finset, are the
sieve support: `primeFactors` is `primeFactorsList.toFinset`, so `dedup` is
harmless.  This is the index set of the split's leaf one. -/
private theorem primeFactorsList_dedup_primeProduct (X δ : ℝ) (n : ℕ) :
    (primeProduct X δ n).primeFactorsList.dedup.toFinset = primeSupport X δ n := by
  rw [List.toFinset_dedup, Nat.toFinset_factors, primeFactors_primeProduct]

/-- Iwaniec page 179 formula 3.4 with the density weight: the Rosser main sum of
a `BoundingSieve` is the alternating sum over the distinct descending prime
sublists of its sifting product, each term carrying the product of the local
densities over the sublist. -/
private theorem mainSum_eq_sublists (s : BoundingSieve) (D β : ℝ) :
    s.mainSum (rosserWeight D β) =
      ((s.prodPrimes.primeFactorsList.dedup.reverse).sublists.map
        (fun t => (-1 : ℝ) ^ t.length * prefixRho D β t *
          ∏ p ∈ t.toFinset, s.nu p)).sum := by
  classical
  have hn : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  let L := s.prodPrimes.primeFactorsList.dedup.reverse
  have hLnodup : L.Nodup := List.nodup_reverse.mpr (List.nodup_dedup _)
  have hLsort : L.Pairwise (· ≥ ·) := List.pairwise_reverse.mpr
    ((Nat.isChain_primeFactorsList s.prodPrimes).pairwise.sublist (List.dedup_sublist _))
  have hLprime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp (List.mem_reverse.mp hp))
  have hLdvd : L.prod ∣ s.prodPrimes := by
    have hd := (List.dedup_sublist s.prodPrimes.primeFactorsList).prod_dvd_prod
    rw [Nat.prod_primeFactorsList hn] at hd
    simpa only [L, List.prod_reverse] using hd
  have hprops : ∀ t ∈ L.sublists.toFinset,
      (∀ p ∈ t, Nat.Prime p) ∧ t.Pairwise (· ≥ ·) ∧ t.Nodup := by
    intro t ht
    have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
    exact ⟨fun p hp => hLprime p (hsub.subset hp), hLsort.sublist hsub, hLnodup.sublist hsub⟩
  have hbij : (∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod) =
      ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d := by
    apply Finset.sum_bij (fun t _ => t.prod)
    · intro t ht
      obtain ⟨hp, hs, hnd⟩ := hprops t ht
      have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hsub.prod_dvd_prod.trans hLdvd, hn⟩,
          descending_prime_product_squarefree t hp hs hnd⟩
    · intro t ht u hu he
      obtain ⟨htp, hts, htnd⟩ := hprops t ht
      obtain ⟨hup, hus, hund⟩ := hprops u hu
      have htF := descending_prime_factorization t htp hts
      have huF := descending_prime_factorization u hup hus
      rw [he] at htF
      exact htF.symm.trans huF
    · intro d hd
      obtain ⟨hdiv, hdSq⟩ := Finset.mem_filter.mp hd
      have hdn : d ≠ 0 := (Nat.pos_of_mem_divisors hdiv).ne'
      have htnd : d.primeFactorsList.reverse.Nodup :=
        List.nodup_reverse.mpr ((Nat.squarefree_iff_nodup_primeFactorsList hdn).mp hdSq)
      have hts : d.primeFactorsList.reverse.Pairwise (· ≥ ·) :=
        List.pairwise_reverse.mpr (Nat.isChain_primeFactorsList d).pairwise
      have hsubset : d.primeFactorsList.reverse ⊆ L := by
        intro p hp
        apply List.mem_reverse.mpr
        apply List.mem_dedup.mpr
        exact (Nat.primeFactorsList_sublist_of_dvd (Nat.dvd_of_mem_divisors hdiv) hn).subset
          (List.mem_reverse.mp hp)
      have htL : List.Sublist d.primeFactorsList.reverse L :=
        List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htnd hsubset) hts hLsort
      refine ⟨d.primeFactorsList.reverse, List.mem_toFinset.mpr (List.mem_sublists.mpr htL), ?_⟩
      rw [List.prod_reverse, Nat.prod_primeFactorsList hdn]
    · intro t ht
      rfl
  have hfilter : (∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d) =
      ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnsq : ¬ Squarefree d := by simpa only [Finset.mem_filter, hd, true_and] using hnot
    rw [rosserWeight_not_squarefree D β d hnsq, zero_mul]
  have hterm : ∀ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod =
      (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p := by
    intro t ht
    obtain ⟨htp, hts, htnd⟩ := hprops t ht
    rw [rosserWeight_prod D β t htp hts htnd]
    have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
      have h := List.prod_toFinset (f := id) htnd
      simpa using h
    have hndid : ∏ p ∈ t.toFinset, s.nu p = s.nu (∏ p ∈ t.toFinset, p) :=
      (ArithmeticFunction.IsMultiplicative.map_prod_of_prime s.nu_mult t.toFinset
        (fun p hp => htp p (List.mem_toFinset.mp hp))).symm
    rw [hndid, hprod]
  calc s.mainSum (rosserWeight D β)
      = ∑ d ∈ s.prodPrimes.divisors, rosserWeight D β d * s.nu d := rfl
    _ = ∑ d ∈ s.prodPrimes.divisors.filter Squarefree, rosserWeight D β d * s.nu d :=
        hfilter.symm
    _ = ∑ t ∈ L.sublists.toFinset, rosserWeight D β t.prod * s.nu t.prod := hbij.symm
    _ = ∑ t ∈ L.sublists.toFinset,
          (-1 : ℝ) ^ t.length * prefixRho D β t * ∏ p ∈ t.toFinset, s.nu p :=
        Finset.sum_congr rfl hterm
    _ = _ := List.sum_toFinset _ (List.nodup_sublists.mpr hLnodup)

/-- LEAF: step one of the proof, the local product identity.  The strict
product below the close cutoff equals the product of the one minus local
factors taken over the distinct prime factors of the squarefree sieve product.
A prime outside the sieve support carries density zero, so its factor is one
on both sides and the two products agree.  This is an identity in the
definitions alone: it names no main sum, no level and no dimension estimate. -/
theorem strictProduct_eq_primeFactors_prod (X δ : ℝ) (n : ℕ) :
    strictProduct X δ n =
      ∏ p ∈ (primeProduct X δ n).primeFactorsList.dedup.toFinset, (1 - density n p) := by
  rw [strictProduct_eq_prod_primeSupport, primeFactorsList_dedup_primeProduct]

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
  classical
  have h := mainSum_eq_sublists (sieveModel X B δ ε n hn) D β
  rw [show (sieveModel X B δ ε n hn).prodPrimes = primeProduct X δ n from rfl] at h
  rw [h]
  rw [← List.sum_toFinset _
    (List.nodup_sublists.mpr (List.nodup_reverse.mpr (List.nodup_dedup _)))]
  apply Finset.sum_congr rfl
  intro t ht
  have hnu : ∀ p : ℕ, (sieveModel X B δ ε n hn).nu p = density n p := fun p => rfl
  simp only [hnu]
  have hsub := List.mem_sublists.mp (List.mem_toFinset.mp ht)
  have hnd : t.Nodup :=
    (List.nodup_reverse.mpr (List.nodup_dedup _)).sublist hsub
  have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactorsList
      (List.mem_dedup.mp (List.mem_reverse.mp (hsub.subset hp)))
  have hprod : (∏ p ∈ t.toFinset, p) = t.prod := by
    have hh := List.prod_toFinset (f := id) hnd
    simpa using hh
  have hndid : ∏ p ∈ t.toFinset, density n p = density n t.prod := by
    rw [← hprod]
    exact (ArithmeticFunction.IsMultiplicative.map_prod_of_prime (density_isMultiplicative n)
      (f := densityFunction n) t.toFinset
      (fun p hp => hprime p (List.mem_toFinset.mp hp))).symm
  rw [hndid]

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
