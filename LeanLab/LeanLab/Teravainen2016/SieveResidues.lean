/-
P0076 Lemma 5.4 display 5.5, pages 19 to 20.
Equivalence of the local product weight with the integer coprimality conditions.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.CompositeLemma54

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Integer coprimality is exclusion of the prime divisors of a nonzero modulus. -/
theorem int_coprime_primeFactors_iff {q : ℕ} (hq : q ≠ 0) (z : ℤ) :
    IsCoprime z (q : ℤ) ↔ ∀ p ∈ q.primeFactors, ¬ (p : ℤ) ∣ z := by
  constructor
  · intro h p hp hpd
    have hd := Int.dvd_gcd hpd (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors hp))
    rw [Int.isCoprime_iff_gcd_eq_one.mp h] at hd
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one (by exact_mod_cast hd)
  · intro h
    apply isCoprime_of_primes
    intro p hp hpz hpq
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd_natCast.mp hpq, hq⟩) hpz

/-- The local product weight is the exact indicator of the two integer sieve restrictions. -/
theorem localSieveWeight_product_eq (q : ℕ) [NeZero q] (W V b : ℤ) (n : ℕ) :
    (∏ p : q.primeFactors, localSieveWeight p W V b (n : ZMod p)) =
      if IsCoprime (W * V * n + b) (q : ℤ) ∧
        (∀ p ∈ q.primeFactors, p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * V * n + b - 1)
      then (1 : ℂ) else 0 := by
  let L : ℤ := W * V * n + b
  have hw (p : q.primeFactors) : localSieveWeight p W V b (n : ZMod p) =
      if ¬ (p : ℤ) ∣ L ∧ ((p : ℕ) % 4 = 3 ∧ (p : ℕ) ≠ 3 → ¬ (p : ℤ) ∣ L - 1)
      then (1 : ℂ) else 0 := by
    have hc : (L : ZMod p) = (W : ZMod p) * V * (n : ZMod p) + b := by
      dsimp [L]
      push_cast
      rfl
    have h0 : (L : ZMod p) ≠ 0 ↔ ¬ (p : ℤ) ∣ L :=
      not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd L p)
    have h1 : (L : ZMod p) ≠ 1 ↔ ¬ (p : ℤ) ∣ L - 1 := by
      rw [← sub_ne_zero, ← Int.cast_one, ← Int.cast_sub]
      exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd (L - 1) p)
    unfold localSieveWeight
    rw [← hc]
    simp only [h0, h1]
  simp_rw [hw]
  rw [Fintype.prod_boole]
  simp only [int_coprime_primeFactors_iff (NeZero.ne q)]
  congr 1
  simp only [Subtype.forall, forall_and, and_imp]
  rfl

/-- The integer representative form of the paper sieve sum. -/
noncomputable def integerSieveSum (q : ℕ) (W V b : ℤ) (a : ℕ) : ℂ :=
  ∑ n ∈ (range q).filter (fun n : ℕ => IsCoprime (W * V * n + b) (q : ℤ) ∧
    (∀ p ∈ q.primeFactors, p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * V * n + b - 1)),
    eC ((a : ℝ) * n / q)

/-- The finite local product is exactly the integer sum in display 5.5. -/
theorem compositeSieveSum_eq_integer (q : ℕ) [NeZero q] (W V b : ℤ) (a : ℕ) :
    compositeSieveSum q W V b a = integerSieveSum q W V b a := by
  unfold compositeSieveSum integerSieveSum
  simp_rw [localSieveWeight_product_eq]
  rw [sum_filter, ← sum_zmod_val (fun n => if IsCoprime (W * V * n + b) (q : ℤ) ∧
      (∀ p ∈ q.primeFactors, p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ W * V * n + b - 1)
      then eC ((a : ℝ) * n / q) else 0)]
  apply sum_congr rfl
  intro x _
  have hc : ZMod.stdAddChar ((a : ZMod q) * x) = eC ((a : ℝ) * x.val / q) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using stdAddChar_int_nat (p := q) (a : ℤ) x.val
  rw [hc]
  split_ifs <;> simp

/-- The exact integer sieve sum obeys the complete divisor bound. -/
theorem integerSieveSum_norm_le_divisors (q : ℕ) [NeZero q] (W V b : ℤ)
    (a : ℕ) (ha : a.Coprime q) : ‖integerSieveSum q W V b a‖ ≤ (q.divisors.card : ℝ) := by
  rw [← compositeSieveSum_eq_integer]
  exact compositeSieveSum_norm_le_divisors q W V b a ha

#print axioms int_coprime_primeFactors_iff
#print axioms localSieveWeight_product_eq
#print axioms compositeSieveSum_eq_integer
#print axioms integerSieveSum_norm_le_divisors

end LeanLab.Teravainen2016
