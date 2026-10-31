import LeanLab.Pintz2021.ElementaryTask08

/-!
Finite divisor expansion for P0054 page 5 display 2.4 and page 14 display 4.9.
These are derived helpers for Lemma 2.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.DivisorTask53

open Finset ElementaryTask08

attribute [local instance] Classical.propDecidable

/-- The odd squarefree divisors of a nonzero integer. -/
noncomputable def oddSquarefreeDivisors (m : ℕ) : Finset ℕ :=
  m.divisors.filter fun d => Odd d ∧ Squarefree d

/-- Subset products are exactly the odd squarefree divisors. -/
theorem subset_products_eq {m : ℕ} (hm : m ≠ 0) :
    ((m.primeFactors.filter fun p => 2 < p).powerset.image
      (fun s => ∏ p ∈ s, p)) = oddSquarefreeDivisors m := by
  ext d
  constructor
  · intro hd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    have hsub := mem_powerset.mp hs
    have hp : ∀ p ∈ s, p.Prime := fun p h =>
      Nat.prime_of_mem_primeFactors (mem_filter.mp (hsub h)).1
    have hodd : Odd (∏ p ∈ s, p) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h
      obtain ⟨p, hps, hpd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
      have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hp p hps)).mp hpd
      have := (mem_filter.mp (hsub hps)).2
      omega
    have hsq : Squarefree (∏ p ∈ s, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hps q hqs hpq
        exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hps) (hp q hqs)).mpr hpq)
      · intro p hps
        exact (hp p hps).squarefree
    have hdvd : (∏ p ∈ s, p) ∣ m :=
      (prod_dvd_prod_of_subset _ _ _ (fun p h => (mem_filter.mp (hsub h)).1)).trans
        m.prod_primeFactors_dvd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hm⟩, hodd, hsq⟩
  · intro hd
    obtain ⟨hdm, hodd, hsq⟩ := mem_filter.mp hd
    have hdvd := (Nat.mem_divisors.mp hdm).1
    refine mem_image.mpr ⟨d.primeFactors, mem_powerset.mpr ?_,
      Nat.prod_primeFactors_of_squarefree hsq⟩
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    refine mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp', hpd.trans hdvd, hm⟩, ?_⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
    exact lt_of_le_of_ne hp'.two_le (Ne.symm hp2)

end LeanLab.Pintz2021.DivisorTask53

#print axioms LeanLab.Pintz2021.DivisorTask53.subset_products_eq
