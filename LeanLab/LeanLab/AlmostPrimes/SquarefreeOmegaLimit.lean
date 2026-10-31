import LeanLab.AlmostPrimes.Statements

/-!
# Square-freeness does not bound the number of prime factors

AI wrote the Lean code. Goldbach is open.
Source context: BJS, https://arxiv.org/abs/2207.09452, Section 10, page 63.
The paper uses Dudek's square-free representation as one ingredient of Theorem 5.
These lab helper lemmas show why square-freeness alone does not give the
two-factor remainder required by Chen's theorem. They do not refute either result.
The proof uses primorials and Euclid's infinitude of primes, with no analytic input.
-/

namespace LeanLab.AlmostPrimes.SquarefreeOmegaLimit

/-- The number of prime factors of a primorial is the number of primes in its range. -/
theorem bigOmega_primorial (n : ℕ) : bigOmega (primorial n) = Nat.primeCounting n := by
  have h := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
    (primorial_ne_zero n)).mpr (squarefree_primorial n)
  rw [bigOmega_eq_cardFactors, ← h, ArithmeticFunction.cardDistinctFactors_apply,
    ← List.card_toFinset, Nat.toFinset_factors, primeFactors_primorial,
    Nat.primesLE_card_eq_primeCounting]

/-- Positive square-free numbers have arbitrarily many prime factors. -/
theorem exists_squarefree_bigOmega_gt (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Squarefree m ∧ k < bigOmega m := by
  obtain ⟨n, hn⟩ := Nat.surjective_primeCounting (k + 1)
  refine ⟨primorial n, primorial_pos n, squarefree_primorial n, ?_⟩
  rw [bigOmega_primorial, hn]
  omega

/-- Square-freeness alone supplies no uniform bound on Omega. -/
theorem no_uniform_squarefree_bigOmega (k : ℕ) :
    ¬ ∀ m : ℕ, 0 < m → Squarefree m → bigOmega m ≤ k := by
  intro h
  obtain ⟨m, hm, hs, hk⟩ := exists_squarefree_bigOmega_gt k
  exact (not_le_of_gt hk) (h m hm hs)

/-- A concrete square-free remainder already exceeds the two-factor bound. -/
theorem thirty_instance : Squarefree (30 : ℕ) ∧ bigOmega 30 = 3 := by
  constructor
  · exact (Nat.squarefree_iff_nodup_primeFactorsList (by decide : (30 : ℕ) ≠ 0)).mpr
      (by simp [Nat.primeFactorsList_ofNat])
  · norm_num [bigOmega, Nat.primeFactorsList_ofNat]

end LeanLab.AlmostPrimes.SquarefreeOmegaLimit

#print axioms LeanLab.AlmostPrimes.SquarefreeOmegaLimit.bigOmega_primorial
#print axioms LeanLab.AlmostPrimes.SquarefreeOmegaLimit.exists_squarefree_bigOmega_gt
#print axioms LeanLab.AlmostPrimes.SquarefreeOmegaLimit.no_uniform_squarefree_bigOmega
#print axioms LeanLab.AlmostPrimes.SquarefreeOmegaLimit.thirty_instance
