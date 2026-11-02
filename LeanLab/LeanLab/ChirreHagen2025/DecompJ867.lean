import LeanLab.ChirreHagen2025.Statements
import LeanLab.ChirreHagen2025.Additional122

/-!
Decomposition of P0075 Lemma A.1 part 1, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.DecompJ867

open Real

/-- LEAF. P0075 page 13, sum split at n0 = 26355867. -/
theorem leaf_split_n0 (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∑' p : Nat.Primes, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) =
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n0),
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) +
    (∑' p : {p : Nat.Primes // n0 < (p : ℕ)},
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := by
  sorry

/-- LEAF. P0075 page 13, bound the finite sum up to n0. -/
theorem leaf_finite_sum_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n0),
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) < 1.721381 := by
  sorry

/-- LEAF. P0075 page 13, lower bound for primes greater than n0.
Uses p_n > n log n for n ≥ 1. -/
theorem leaf_prime_lower_bound (p : Nat.Primes) (n0 : ℕ) (hn0 : n0 = 26355867) (hp : n0 < (p : ℕ)) :
    ∃ n : ℕ, n0 < n ∧ (n : ℝ) * Real.log (n : ℝ) < (p : ℝ) := by
  sorry

/-- LEAF. P0075 page 13, bounding the tail sum by an integral. -/
theorem leaf_tail_sum_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∑' p : {p : Nat.Primes // n0 < (p : ℕ)},
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) ≤
    (∫ x in Set.Ioi (n0 : ℝ), Real.log (x * Real.log x) /
      (Real.sqrt (x * Real.log x) * (x * Real.log x - 1))) := by
  sorry

/-- LEAF. P0075 page 14, upper bound for the integral. -/
theorem leaf_integral_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∫ x in Set.Ioi (n0 : ℝ), Real.log (x * Real.log x) /
      (Real.sqrt (x * Real.log x) * (x * Real.log x - 1))) < 0.000104 := by
  sorry

/-- LEAF. P0075 page 13, summability of the series. -/
theorem leaf_summability_lemma :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) /
      (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := by
  sorry

/-- P0075 Lemma A.1 part 1 assembled. -/
theorem lemmaA1_part1_assembled : Additional122.lemmaA1_part1 := by
  have hn0_eq : 26355867 = 26355867 := rfl
  have hsplit := leaf_split_n0 26355867 hn0_eq
  have hfinite := leaf_finite_sum_bound 26355867 hn0_eq
  have htail := leaf_tail_sum_bound 26355867 hn0_eq
  have hint := leaf_integral_bound 26355867 hn0_eq
  constructor
  · exact leaf_summability_lemma
  · calc (∑' p : Nat.Primes, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1)))
      _ = (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 26355867), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) + (∑' p : {p : Nat.Primes // 26355867 < (p : ℕ)}, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := hsplit
      _ ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 26355867), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) + (∫ x in Set.Ioi (26355867 : ℝ), Real.log (x * Real.log x) / (Real.sqrt (x * Real.log x) * (x * Real.log x - 1))) := by
        exact add_le_add le_rfl htail
      _ < 1.721381 + 0.000104 := add_lt_add hfinite hint
      _ < 1.7215 := by norm_num

end LeanLab.ChirreHagen2025.DecompJ867
