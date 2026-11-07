/-
Split of `r2_prime_power_bound` (`BhowmikGrimmelt2026/DecompJ1034.lean`).

The statement splits `r2 N = Σ_{a+b=N} Λ(a)Λ(b)` at an even `N` that is *not* a Goldbach sum.
Two facts carry the split:

* the pairs `(a, b)` in which both entries are prime contribute nothing, because there is no such
  pair at an `N` that is not a Goldbach sum — this is the only place the hypothesis
  `¬ IsGoldbachSum N` is used;
* what is left is carried by pairs whose first entry is not prime, and by pairs whose first entry
  is prime while the second is not. Each of those two masses is bounded by three quarters of the
  right-hand side; twice three quarters is the factor `3/2` of the statement.

Note on the exponent in the statement: `(N : ℝ)^(1/2)` is `HPow.hPow` with a **`ℕ`** exponent, so
`(1 : ℕ) / 2 = 0` and the factor is `(N : ℝ) ^ 0 = 1`. Leaves 2 and 3 are therefore stated with
the same exponent, and nothing in this file depends on `√N` versus `1` beyond the shape of the
right-hand side.
-/
import LeanLab.BhowmikGrimmelt2026.DecompJ1034

namespace LeanLab.BhowmikGrimmelt2026

/-! ## The three-way split of the antidiagonal sum -/

/-- `r2 N` is the sum of three parts over the same antidiagonal: the part where both entries are
prime, the part where the first entry is not prime, and the part where the first entry is prime and
the second is not. This is a pointwise case distinction on the two primality conditions, so it
holds for every `N` and needs no hypothesis. -/
private lemma r2_three_parts (N : ℕ) :
    r2 N =
      (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if x.1.Prime ∧ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      + (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if ¬ x.1.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      + (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if x.1.Prime then
          (if ¬ x.2.Prime then
            ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)
          else 0)) := by
  unfold r2
  conv_rhs => rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h1 : x.1.Prime <;> by_cases h2 : x.2.Prime <;> simp [h1, h2]

/-! ## The leaves -/

/-- LEAF. Step 1 of the proof: the part of the von Mangoldt sum over pairs whose two entries are
both prime is zero at an `N` that is not a Goldbach sum. Such a pair would be a pair of primes with
`p + q = N`, which is exactly what the hypothesis excludes; every remaining term is replaced by
`0`. -/
theorem leaf_both_prime_part_vanishes (N : ℕ) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if x.1.Prime ∧ x.2.Prime then
        ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)) = 0 := by
  sorry

/-- LEAF. Step 2 of the proof: the mass carried by the pairs whose first entry is not prime — that
is, since `Λ` vanishes off the prime powers, whose first entry is a proper prime power — is at most
three quarters of the right-hand side. This is the first half of the count of proper prime power
representations of `N`, and it is the only estimate in the split that is not a formal identity. -/
theorem leaf_first_entry_not_prime_mass (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if ¬ x.1.Prime then
        ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      ≤ 3/4 * ((N : ℝ)^(1/2) * (Real.log (N : ℝ))^3) := by
  sorry

/-- LEAF. Step 3 of the proof: the mass carried by the pairs whose first entry is prime while the
second is not is at most three quarters of the right-hand side. Together with step 2 this is the
full proper prime power count: at an `N` that is not a Goldbach sum, a term with both entries prime
never occurs, so every surviving pair has a non-prime entry, and the two steps cover the two ways
that can happen. -/
theorem leaf_second_entry_not_prime_mass (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if x.1.Prime then
        (if ¬ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)
        else 0))
      ≤ 3/4 * ((N : ℝ)^(1/2) * (Real.log (N : ℝ))^3) := by
  sorry

/-! ## The assembly -/

/-- The statement of `r2_prime_power_bound`, derived from the three steps above. The whole content
sits in leaves 2 and 3; the assembly is the case distinction of `r2_three_parts` and the vanishing
of leaf 1. -/
theorem r2_prime_power_bound_split (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
   r2 N ≤ 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 := by
  have hu : 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3
      = 3/2 * ((N : ℝ)^(1/2) * (Real.log (N : ℝ))^3) := by ring
  have h1 := leaf_both_prime_part_vanishes N h_not_G
  have h2 := leaf_first_entry_not_prime_mass N hN h_not_G
  have h3 := leaf_second_entry_not_prime_mass N hN h_not_G
  have hsp := r2_three_parts N
  rw [hu]
  linarith [hsp, h1, h2, h3]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.r2_prime_power_bound_split
