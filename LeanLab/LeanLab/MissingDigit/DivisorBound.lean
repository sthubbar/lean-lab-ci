import LeanLab.MissingDigit.Statements

/-!
Kim 2024, arXiv 2412.19975v1, page 6, before equation 1.9.
Elementary divisor function bookkeeping for d2 squared at most d4.
The lab dk definition is identified with powers under Dirichlet convolution.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.MissingDigit.KimSeries

open Finset
open scoped ArithmeticFunction.zeta

/-- The recursive divisor count is the k-fold Dirichlet convolution power of zeta. -/
theorem dk_eq_zeta_pow : ∀ k n : ℕ, dk k n = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k) n := by
  intro k
  induction k with
  | zero =>
    intro n
    by_cases h : n = 1 <;> simp [dk, ArithmeticFunction.one_apply, h]
  | succ k ih =>
    intro n
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply]
    change (∑ d ∈ n.divisors, dk k (n / d)) =
      ∑ d ∈ n.divisors, ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k) d
    rw [Nat.sum_div_divisors]
    exact Finset.sum_congr rfl (fun d _ => ih d)

/-- The divisor counts multiply on coprime arguments. -/
theorem dk_mul_of_coprime (k : ℕ) {a b : ℕ} (h : Nat.Coprime a b) :
    dk k (a * b) = dk k a * dk k b := by
  simp only [dk_eq_zeta_pow]
  exact (ArithmeticFunction.isMultiplicative_zeta.pow (k := k)).map_mul_of_coprime h

/-- On a prime power the next divisor function is a finite sum of the previous one. -/
theorem dk_succ_prime_pow {p : ℕ} (hp : p.Prime) (k a : ℕ) :
    dk (k + 1) (p ^ a) = ∑ j ∈ Finset.range (a + 1), dk k (p ^ j) := by
  change (∑ d ∈ (p ^ a).divisors, dk k (p ^ a / d)) = _
  rw [Nat.sum_div_divisors, Nat.sum_divisors_prime_pow hp]

end LeanLab.MissingDigit.KimSeries
