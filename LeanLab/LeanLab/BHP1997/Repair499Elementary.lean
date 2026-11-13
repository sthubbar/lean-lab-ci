/-
P0069 Baker Harman Pintz 1997, pages 50 and 51, display 5.15.
At a prime argument both deleted sums vanish. The normalized coefficient
therefore equals its normalization factor. This checks the prime contribution
without using any distribution or exceptional set input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerShortC165

namespace LeanLab.BHP1997.LowerShortC165
open Classical Decomp132

/-- Pages 50 and 51, display 5.15: a prime has no ordered pair of distinct
prime divisors, so neither deleted sum contributes at a prime argument. -/
theorem deleted_sums_eq_zero_of_prime499 (ε x : ℝ) {m : ℕ} (hm : m.Prime) :
    lowerTwoTerms ε x m = 0 ∧ lowerFourTerms ε x m = 0 := by
  have heq : ∀ p ∈ m.divisors, p.Prime → p = m := by
    intro p hp hprime
    exact (Nat.prime_dvd_prime_iff_eq hprime hm).mp (Nat.dvd_of_mem_divisors hp)
  constructor
  · unfold lowerTwoTerms
    refine Finset.sum_eq_zero fun p1 hp1 => Finset.sum_eq_zero fun p2 hp2 => ?_
    split_ifs with h
    · have h1 := heq p1 hp1 h.1
      have h2 := heq p2 hp2 h.2.1
      have hlt := h.2.2.1
      omega
    · rfl
  · unfold lowerFourTerms
    refine Finset.sum_eq_zero fun p1 hp1 => Finset.sum_eq_zero fun p2 hp2 =>
      Finset.sum_eq_zero fun p3 _ => Finset.sum_eq_zero fun p4 _ => ?_
    split_ifs with h
    · have h1 := heq p1 hp1 h.1
      have h2 := heq p2 hp2 h.2.1
      have hlt := h.2.2.2.2.1
      omega
    · rfl

/-- Page 51, the subtraction defining b0: its raw value at a prime is one. -/
theorem rawLower_eq_one_of_prime499 (ε x : ℝ) {m : ℕ} (hm : m.Prime) :
    rawLower ε x m = 1 := by
  obtain ⟨h2, h4⟩ := deleted_sums_eq_zero_of_prime499 ε x hm
  simp [rawLower, primeWeight, hm, h2, h4]

/-- Pages 51 and 52 with the existing U-1624 normalization: at a prime,
the normalized lower coefficient is exactly the normalization factor. -/
theorem lowerShortWeight_eq_factor_of_prime499 (ω : ℝ → ℝ) (ε x : ℝ)
    {m : ℕ} (hm : m.Prime) :
    lowerShortWeight ω ε x m = lowerFactor ω ε x m := by
  simp [lowerShortWeight, rawLower_eq_one_of_prime499 ε x hm]

end LeanLab.BHP1997.LowerShortC165
