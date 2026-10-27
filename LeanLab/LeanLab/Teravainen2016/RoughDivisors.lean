/-
P0076 Lemma 5.3 proof, page 21. The divisor bound for integers with large prime factors.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Transference

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A prime factor at least 32 pays for the fifth power of its divisor count. -/
theorem prime_power_divisor_factor_le {p : ℕ} (hp : 32 ≤ p) (k : ℕ) :
    (k + 1) ^ 5 ≤ p ^ k := by
  calc
    _ ≤ (2 ^ k) ^ 5 := Nat.pow_le_pow_left (Nat.succ_le_of_lt k.lt_two_pow_self) 5
    _ = (32 : ℕ) ^ k := by rw [← pow_mul, Nat.mul_comm k 5, pow_mul]; norm_num
    _ ≤ _ := Nat.pow_le_pow_left hp k

/-- If every prime factor of q is at least 32, tau q to the fifth is at most q. -/
theorem rough_divisor_card_pow_five {q : ℕ} (hq : q ≠ 0)
    (hrough : ∀ p ∈ q.primeFactors, 32 ≤ p) : q.divisors.card ^ 5 ≤ q := by
  rw [Nat.card_divisors hq, ← prod_pow]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
      prod_le_prod (fun p hp => prime_power_divisor_factor_le (hrough p hp) _)
    _ = q := (Nat.prod_primeFactors_pow_factorization hq).symm

/-- The real fifth power divisor bound used on page 21. -/
theorem rough_divisor_card_le_fifth {q : ℕ} (hq : q ≠ 0)
    (hrough : ∀ p ∈ q.primeFactors, 32 ≤ p) :
    (q.divisors.card : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) := by
  have hnat := rough_divisor_card_pow_five hq hrough
  have hr : ((q.divisors.card : ℝ) ^ (5 : ℕ)) ≤ (q : ℝ) := by exact_mod_cast hnat
  have hh := Real.rpow_le_rpow (by positivity) hr (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have he : ((q.divisors.card : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) = q.divisors.card := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [he] at hh

/-- Coprimality with W excludes every prime factor at most w. -/
theorem prime_factor_gt_w {J w q p : ℕ} (hJ : 5 ≤ J)
    (hcop : IsCoprime (q : ℤ) (WW J w)) (hp : p ∈ q.primeFactors) : w < p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdq : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  by_contra hwp
  have hpw : p ≤ w := by omega
  have hpdW : (p : ℤ) ∣ WW J w := by
    by_cases hp2 : p = 2
    · subst p
      simpa [WW] using two_pow_dvd_Wmod (J := J) (k := 1) (Sw w) (by omega)
    by_cases hp3 : p = 3
    · subst p
      exact (by norm_num : (3 : ℤ) ∣ 27).trans (dvd27_Wmod J (Sw w))
    have hp5 : 5 ≤ p := by
      by_contra h
      have hp4 : p ≤ 4 := by omega
      interval_cases p <;> norm_num at hprime <;> omega
    exact dvd_Wmod_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp5, hpw⟩, hprime⟩)
  have hd := Int.dvd_gcd hpdq hpdW
  rw [Int.isCoprime_iff_gcd_eq_one.mp hcop] at hd
  have hone : p ∣ 1 := by exact_mod_cast hd
  exact hprime.not_dvd_one hone

/-- A direct elementary consequence for the modulus in display 3.3. -/
theorem divisor_card_le_fifth_of_coprime_WW {J w q : ℕ} (hJ : 5 ≤ J) (hw : 32 ≤ w)
    (hq : q ≠ 0) (hcop : IsCoprime (q : ℤ) (WW J w)) :
    (q.divisors.card : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 5) := by
  apply rough_divisor_card_le_fifth hq
  intro p hp
  have hh := prime_factor_gt_w hJ hcop hp
  omega

example : (Nat.divisors 1).card = 1 := by decide

#print axioms prime_power_divisor_factor_le
#print axioms rough_divisor_card_pow_five
#print axioms rough_divisor_card_le_fifth
#print axioms prime_factor_gt_w
#print axioms divisor_card_le_fifth_of_coprime_WW

end LeanLab.Teravainen2016
