/-
Split of `bjs_all` into leaves.

The whole statement is cut at the corrected Chen threshold `Real.exp (Real.exp 32.73)`:

* below the threshold the small case uses the square-free remainder input (`N = p + m` with `m`
  square-free) and the counting estimate which turns `m ≤ exp (exp 32.73)` into
  `Ω m ≤ exp 29.3` for a square-free `m`: there the number of prime factors with multiplicity
  equals the number of distinct prime factors, and the distinct count is bounded by the count of
  primes below a short window above `exp 32.73`;
* above the threshold the large case is `bjs_chen_3273`, which gives `Ω ≤ 2` and hence the
  constant `k = 2`, with `2 ≤ exp 29.3`.

The leaves below are the two open steps of the small case, plus the multiplicity identity linking
them. Each is strictly weaker than `bjs_all`: the first is restricted to one range and asserts no
factor bound, the second is an estimate about one integer with no prime decomposition in it, the
third is a multiplicity identity for square-free integers.

AI-written Lean code. Checked only by the Lean kernel.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

/-- LEAF 1 of 3, the square-free remainder step on the small range: an even `N ≥ 4` that does not
exceed `exp (exp 32.73)` splits as a prime plus a positive square-free integer. This is the
Dudek-type remainder input; it asserts no bound on the number of prime factors of the
remainder. -/
theorem leaf_squarefree_remainder (N : ℕ) (hEven : Even N) (hN : 4 ≤ N)
    (hsmall : (N : ℝ) ≤ Real.exp (Real.exp 32.73)) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  sorry

/-- LEAF 2 of 3, the counting estimate of the small range: a positive integer below
`exp (exp 32.73)` has at most `exp 29.3` distinct prime factors. The constant is the one obtained
by counting the primes in a window just above `exp 32.73`; it is the step that fixes `29.3`. -/
theorem leaf_card_primeFactors_le_exp (m : ℕ) (hm : 0 < m)
    (hmX : (m : ℝ) ≤ Real.exp (Real.exp 32.73)) :
    ((m.primeFactors.card : ℕ) : ℝ) ≤ Real.exp 29.3 := by
  sorry

/-- LEAF 3 of 3, the multiplicity identity used to pass from the distinct prime factors to
`bigOmega`: for a positive square-free integer the number of prime factors counted with
multiplicity is the number of distinct prime factors. -/
theorem leaf_bigOmega_eq_card_of_squarefree (m : ℕ) (hm : 0 < m) (hsq : Squarefree m) :
    bigOmega m = m.primeFactors.card := by
  sorry

/-- `bjs_all` assembled from the three leaves: the small case below `exp (exp 32.73)` runs through
`LEAF 1` and `LEAF 2` with `k = bigOmega m = m.primeFactors.card`, and the large case takes
`k = 2` from `bjs_chen_3273`. -/
theorem bjs_all_split :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧ PrimePlusAlmostPrime k N := by
  intro N hEven hN
  by_cases hsmall : (N : ℝ) ≤ Real.exp (Real.exp 32.73)
  · obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := leaf_squarefree_remainder N hEven hN hsmall
    refine ⟨bigOmega m, ?_, p, m, hp, hm, hNpm, le_rfl⟩
    rw [leaf_bigOmega_eq_card_of_squarefree m hm hsq]
    refine leaf_card_primeFactors_le_exp m hm (le_trans ?_ hsmall)
    exact_mod_cast (by omega : m ≤ N)
  · refine ⟨2, ?_, bjs_chen_3273 N hEven (not_le.mp hsmall)⟩
    have h := Real.add_one_le_exp 29.3
    push_cast
    linarith

end LeanLab.AlmostPrimes

#print axioms LeanLab.AlmostPrimes.bjs_all_split
