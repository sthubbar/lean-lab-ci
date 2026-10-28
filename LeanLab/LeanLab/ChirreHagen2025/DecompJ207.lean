import LeanLab.ChirreHagen2025.Statements
import LeanLab.ChirreHagen2025.Additional122

/-!
Decomposition of P0075 Lemma A.1 part 2, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.DecompJ207

open Real

/-- LEAF. P0075 page 14, equality of sums.
Equality between the sum of Λ(n)^2/n^2 and sum over primes. -/
theorem mangoldt_sum_eq_prime_sum :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) =
    (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
  sorry

/-- LEAF. P0075 page 14, inequality.
1 / (p^2 - 1) ≤ 1 / (p^2 - p). -/
theorem prime_fraction_le (p : ℕ) (hp : p.Prime) :
    1 / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
  have hp_ge : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.two_le
  have h1 : 0 < (p : ℝ) ^ 2 - (p : ℝ) := by
    calc
      0 < (2 : ℝ) ^ 2 - (2 : ℝ) := by norm_num
      _ ≤ (p : ℝ) ^ 2 - (p : ℝ) := by
        nlinarith
  apply one_div_le_one_div_of_le h1
  linarith

/-- LEAF. P0075 page 14, sum comparison. -/
theorem prime_sum_le_part3 :
    (∑' (p : Nat.Primes), log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) ≤
    (∑' (p : Nat.Primes), log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) := by
  sorry

/-- LEAF. P0075 page 14, final numerical bound for part 2. -/
theorem mangoldt_sum_bound
    (h_eq : (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) =
      (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)))
    (h_le : (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) ≤
      (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))))
    (h_part3 : (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) < 0.982) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) < 0.8053 := by
  sorry

/-- LEAF. P0075 page 14. -/
theorem lemmaA1_part3_assumed : Additional122.lemmaA1_part3 := by
  sorry

/-- P0075 Lemma A.1 part 2 assembled. -/
theorem lemmaA1_part2_assembled : Additional122.lemmaA1_part2 := by
  exact ⟨Additional122.mangoldt_sq_summable, mangoldt_sum_bound mangoldt_sum_eq_prime_sum prime_sum_le_part3 lemmaA1_part3_assumed.2⟩

end LeanLab.ChirreHagen2025.DecompJ207
