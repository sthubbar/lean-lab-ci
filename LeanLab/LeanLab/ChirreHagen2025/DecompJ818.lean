import LeanLab.ChirreHagen2025.Statements
import LeanLab.ChirreHagen2025.Additional122
import LeanLab.ChirreHagen2025.Summability272
import LeanLab.ChirreHagen2025.TailIntegral297
import LeanLab.ChirreHagen2025.TailNumeric297
import LeanLab.ChirreHagen2025.PrimeSplit297
import Mathlib

/-!
Decomposition of P0075 Lemma A.1 part 1, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.DecompJ818

open Real

/-- LEAF. P0075 page 13, bounding the tail sum by an integral. -/
theorem tail_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
  (∑' n : ℕ, if n0 < n then Real.log ((n : ℝ) * Real.log (n : ℝ)) / (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ) - 1)) else 0)
    ≤ ∫ x in Set.Ici (n0 : ℝ), Real.log (x * Real.log x) / (Real.sqrt (x * Real.log x) * (x * Real.log x - 1)) := by
  simpa only [TailIntegral297.tailWeight, TailIntegral297.weight] using
    TailIntegral297.tail_sum_le_integral n0 (by omega)

/-- LEAF. P0075 page 14, numerical evaluation of the integral tail. -/
theorem tail_integral_bound (n0 : ℝ) (hn0 : n0 = 26355867) :
  (∫ x in Set.Ici n0, Real.log (x * Real.log x) / (Real.sqrt (x * Real.log x) * (x * Real.log x - 1))) < 0.000104 := by
  subst n0
  simpa only [TailIntegral297.tailWeight, TailIntegral297.weight] using
    TailNumeric297.tail_integral_lt

/-- LEAF. P0075 page 14, numerical evaluation of the finite sum. -/
theorem head_sum_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
  (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime n0)), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) < 1.721381 := by
  sorry

/-- LEAF. P0075 page 13, Rosser bound for the n-th prime. -/
theorem nth_prime_lower_bound (n : ℕ) (hn : 1 ≤ n) :
  (n : ℝ) * Real.log (n : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by
  sorry

/-- LEAF. P0075 page 13, sum split into head and tail, summing primes by index. -/
theorem sum_split_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
  (∑' p : Nat.Primes, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) ≤
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime n0)), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) +
    (∑' n : ℕ, if n0 < n then Real.log ((n : ℝ) * Real.log (n : ℝ)) / (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ) - 1)) else 0) := by
  simpa only [TailIntegral297.weight, TailIntegral297.tailWeight] using
    PrimeSplit297.sum_split_of_lower_bound n0 (by omega)
      (fun n hn => nth_prime_lower_bound n (by omega))

/-- LEAF. P0075 page 13, summability of the series. -/
theorem part1_summable : Summable (fun p : Nat.Primes => Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := by
  exact Summability272.part1_summable

/-- P0075 Lemma A.1 part 1, assembled. -/
theorem lemmaA1_part1_assembled : Additional122.lemmaA1_part1 := by
  refine ⟨part1_summable, ?_⟩
  have h1 := sum_split_bound 26355867 rfl
  have h2 := tail_bound 26355867 rfl
  have h3 := tail_integral_bound 26355867 rfl
  have h4 := head_sum_bound 26355867 rfl
  calc
    (∑' p : Nat.Primes, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1)))
      ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime 26355867)), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) +
        (∑' n : ℕ, if 26355867 < n then Real.log ((n : ℝ) * Real.log (n : ℝ)) / (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ) - 1)) else 0) := h1
    _ ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.nth Nat.Prime 26355867)), Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) +
        ∫ x in Set.Ici (26355867 : ℝ), Real.log (x * Real.log x) / (Real.sqrt (x * Real.log x) * (x * Real.log x - 1)) := add_le_add le_rfl h2
    _ < 1.721381 + 0.000104 := add_lt_add h4 h3
    _ = 1.721485 := by norm_num
    _ < 1.7215 := by norm_num

end LeanLab.ChirreHagen2025.DecompJ818
