import LeanLab.AlmostPrimes.SmallRange

/-!
# The limitation of the trivial split

AI wrote the Lean code. Goldbach is open.
This is a negative result about the elementary argument in SmallRange.
It does not refute a paper statement. The split 1 plus N minus 1 stops certifying
an Omega bound k exactly at N = 2 to the k plus 1, plus 1.
Source context: Dudek and Dunn, arXiv 2602.22720, Theorem 1.2, and
Campbell, arXiv 2608.09488, Theorem 1.2. The papers use sieves for the large range.
The boundary calculation here is the lab's own elementary lemma.
-/

namespace LeanLab.AlmostPrimes.TrivialSplitLimit

/-- The first point beyond the SmallRange certificate has Omega k plus one
for the particular choice a = 1 and b = N minus one. -/
theorem trivial_split_boundary (k : ℕ) :
    bigOmega (1 * ((2 ^ (k + 1) + 1) - 1)) = k + 1 := by
  rw [one_mul, Nat.add_sub_cancel, bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two

/-- No fixed k bounds the Omega value of every trivial split. -/
theorem no_uniform_trivial_split (k : ℕ) :
    ¬ ∀ N : ℕ, 2 ≤ N → bigOmega (1 * (N - 1)) ≤ k := by
  intro h
  have hN : 2 ≤ 2 ^ (k + 1) + 1 := by
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hb := h (2 ^ (k + 1) + 1) hN
  rw [trivial_split_boundary] at hb
  omega

/-- The trivial split also has no uniform Omega bound on even integers.
The witness is N = 3 to the k plus one, plus one. -/
theorem no_uniform_even_trivial_split (k : ℕ) :
    ¬ ∀ N : ℕ, Even N → 4 ≤ N → bigOmega (1 * (N - 1)) ≤ k := by
  intro h
  have ho : Odd (3 ^ (k + 1)) := (by decide : Odd (3 : ℕ)).pow
  have he : Even (3 ^ (k + 1) + 1) := ho.add_odd (by decide : Odd (1 : ℕ))
  have hN : 4 ≤ 3 ^ (k + 1) + 1 := by
    rw [pow_succ]
    have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by decide)
    omega
  have hb := h (3 ^ (k + 1) + 1) he hN
  have hw : bigOmega (1 * ((3 ^ (k + 1) + 1) - 1)) = k + 1 := by
    rw [one_mul, Nat.add_sub_cancel, bigOmega_eq_cardFactors]
    exact ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_three
  rw [hw] at hb
  omega

/-- Concrete failed certificates for the bounds 40 and 33. The underlying
existence theorems are unaffected. -/
theorem boundary_instances :
    bigOmega (1 * ((2 ^ 41 + 1) - 1)) = 41 ∧
      bigOmega (1 * ((2 ^ 34 + 1) - 1)) = 34 :=
  ⟨trivial_split_boundary 40, trivial_split_boundary 33⟩

end LeanLab.AlmostPrimes.TrivialSplitLimit

#print axioms LeanLab.AlmostPrimes.TrivialSplitLimit.trivial_split_boundary
#print axioms LeanLab.AlmostPrimes.TrivialSplitLimit.no_uniform_trivial_split
#print axioms LeanLab.AlmostPrimes.TrivialSplitLimit.boundary_instances

#print axioms LeanLab.AlmostPrimes.TrivialSplitLimit.no_uniform_even_trivial_split
