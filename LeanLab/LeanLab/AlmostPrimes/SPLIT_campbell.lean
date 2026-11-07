/-
Split of `campbell` in `AlmostPrimes/Statements.lean` into four leaves, following the
three-range structure recorded in `AlmostPrimes/PROGRESS.md` for that statement:

* `2 ≤ N ≤ N₀ = 117465180365547648498934439`: the short-interval argument on top of the
  maximal prime gap table input;
* `N₀ < N < 10^132`: the finite verification of a positive sieve sum on the middle range;
* `N ≥ 10^132`: the explicit sieve, which produces two positive summands every prime factor
  of which exceeds `N^(2/33)`;
* a positive integer all of whose prime factors exceed `N^(2/33)` has at most 16 prime
  factors with multiplicity, hence `Ω(ab) ≤ 16 + 16 ≤ 33` for two such summands.

Each leaf is weaker than the target and none of them restates it. `campbell_split` is proved
from the four leaves with no `sorry` and does not use `campbell`.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

/-- LEAF 1, the lower range: every `2 ≤ N ≤ N₀` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the short-interval step with
the gap table input, applied below `N₀`. -/
theorem leaf_small_range : ∀ N : ℕ, 2 ≤ N → N ≤ 117465180365547648498934439 →
    TwoAlmostPrimes 33 N := by
  sorry

/-- LEAF 2, the middle range: every `N₀ < N < 10^132` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the finite verification of a
positive sieve sum on the middle range, converted into the sum of two almost primes. -/
theorem leaf_middle_range : ∀ N : ℕ, 117465180365547648498934439 < N → N < 10 ^ 132 →
    TwoAlmostPrimes 33 N := by
  sorry

/-- LEAF 3, the upper range, sieve output: for every `N ≥ 10^132` there are positive `a, b` with
`N = a + b` and every prime factor of `a` and of `b` strictly larger than `N^(2/33)`. This is
what the explicit sieve produces at `z = N^(2/33)`; it does not itself mention `TwoAlmostPrimes`. -/
theorem leaf_large_sieve_output : ∀ N : ℕ, 10 ^ 132 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    N = a + b ∧ (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) ∧
      (∀ p : ℕ, p.Prime → p ∣ b → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) := by
  sorry

/-- LEAF 4, the counting step: a positive `a ≤ N` all of whose prime factors exceed `N^(2/33)`
has at most 16 prime factors with multiplicity, since `a` is then larger than `N^(2/33)` to the
power `Ω a` while `a ≤ N = (N^(2/33))^(33/2)` and `33/2 = 16.5`. -/
theorem leaf_omega_bound_of_large_prime_factors : ∀ (N a : ℕ), 10 ^ 132 ≤ N → 0 < a → a ≤ N →
    (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) → bigOmega a ≤ 16 := by
  sorry

/-- Private helper with a full proof: `Ω` is additive on a product of positive integers. -/
private theorem bigOmega_mul_add {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simp only [bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_mul ha hb

/-- The target statement, assembled from the four leaves. -/
theorem campbell_split : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  intro N h2
  rcases Nat.lt_or_ge 117465180365547648498934439 N with hmid | hlow
  · rcases Nat.lt_or_ge N (10 ^ 132) with hlt | hge
    · exact leaf_middle_range N hmid hlt
    · obtain ⟨a, b, ha, hb, hN, hpa, hpb⟩ := leaf_large_sieve_output N hge
      have hale : a ≤ N := by omega
      have hble : b ≤ N := by omega
      have hoa : bigOmega a ≤ 16 := leaf_omega_bound_of_large_prime_factors N a hge ha hale hpa
      have hob : bigOmega b ≤ 16 := leaf_omega_bound_of_large_prime_factors N b hge hb hble hpb
      refine ⟨a, b, ha, hb, hN, ?_⟩
      rw [bigOmega_mul_add ha.ne' hb.ne']
      omega
  · exact leaf_small_range N h2 hlow

#print axioms campbell_split

end LeanLab.AlmostPrimes
