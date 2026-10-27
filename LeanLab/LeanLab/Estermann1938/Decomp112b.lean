import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Estermann 1938, P0091, page 312, the gcd sum before display 39.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Decomp112b
open scoped BigOperators

/-- CITED. Page 312: the gcd sum is at most 2n times the divisor count of q. -/
def GcdSumBound : Prop :=
  ∀ (q n : ℕ), 0 < q →
    ∑ m ∈ Finset.Icc 1 (2 * n), Nat.gcd q m ≤ 2 * n * q.divisors.card

/-- LEAF. Page 312, first equality: partition the gcd sum by its value. -/
theorem group_gcd (q N : ℕ) (hq : 0 < q) :
    (∑ m ∈ Finset.Icc 1 N, Nat.gcd q m) =
    ∑ v ∈ q.divisors, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.gcd q m = v), v := by
  classical
  symm
  apply Finset.sum_fiberwise_of_maps_to'
  intro m hm
  exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q m, hq.ne'⟩

/-- LEAF. Page 312, first inequality: each gcd fiber lies among the multiples of v. -/
theorem fiber_le_multiples (q N v : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.gcd q m = v), v) ≤
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => v ∣ m), v := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro m hm
  obtain ⟨hm, h⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hm, h ▸ Nat.gcd_dvd_right q m⟩

/-- LEAF. Page 312: v times the number of positive multiples up to N is at most N. -/
theorem multiples_sum_le (N v : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => v ∣ m), v) ≤ N := by
  classical
  have hi : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hi, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
  exact Nat.div_mul_le_self N v

/-- The gcd sum on page 312 assembled from its counting leaves. -/
theorem gcdSumBound : GcdSumBound := by
  intro q n hq
  rw [group_gcd q (2 * n) hq]
  calc
    (∑ v ∈ q.divisors, ∑ m ∈ (Finset.Icc 1 (2 * n)).filter
      (fun m => Nat.gcd q m = v), v) ≤ ∑ v ∈ q.divisors, 2 * n := by
      apply Finset.sum_le_sum
      intro v hv
      exact (fiber_le_multiples q (2 * n) v).trans (multiples_sum_le (2 * n) v)
    _ = _ := by simp [mul_comm]

#print axioms group_gcd
#print axioms fiber_le_multiples
#print axioms multiples_sum_le
#print axioms gcdSumBound

end LeanLab.Estermann1938.Decomp112b
