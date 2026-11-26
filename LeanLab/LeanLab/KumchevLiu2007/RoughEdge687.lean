/-
Kumchev and Liu 2007, P0088, page 15 after display 52.
Elementary bounds for the upper edge of the square window.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.KumchevLiu2007.Task687

open Real Complex MeasureTheory
open scoped BigOperators

/-- P0088 page 15 after display 52: fewer than three distinct prime divisors
can reach z when the integer is below z cubed. -/
theorem prime_divisor_card_le_two (S : Finset ℕ) (n : ℕ) (z : ℝ)
    (hn : 0 < n) (hz : 0 ≤ z) (hsize : (n : ℝ) < z ^ 3)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n ∧ z ≤ (p : ℝ)) : S.card ≤ 2 := by
  by_contra hcard
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  have hp' := hS p hp
  have hq' := hS q hq
  have hr' := hS r hr
  have hpqd : p * q ∣ n :=
    ((Nat.coprime_primes hp'.1 hq'.1).mpr hpq).mul_dvd_of_dvd_of_dvd hp'.2.1 hq'.2.1
  have hrpq : Nat.Coprime (p * q) r :=
    ((Nat.coprime_primes hp'.1 hr'.1).mpr hpr).mul_left
      ((Nat.coprime_primes hq'.1 hr'.1).mpr hqr)
  have hdiv : p * q * r ∣ n := hrpq.mul_dvd_of_dvd_of_dvd hpqd hr'.2.1
  have hle : ((p * q * r : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hdiv
  have hprod : z ^ 3 ≤ (p : ℝ) * q * r := by
    calc
      z ^ 3 = z * z * z := by ring
      _ ≤ (p : ℝ) * q * r := mul_le_mul
        (mul_le_mul hp'.2.2 hq'.2.2 hz (Nat.cast_nonneg p)) hr'.2.2 hz
        (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q))
  push_cast at hle
  linarith

/-- P0088 page 11 Case 1 and page 15 display 52: each prime divisor
contributes at most three D terms of modulus at most one. -/
theorem small_divisor_block_norm_le (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (f : ℕ → ℕ → ℂ) (n : ℕ) (z D : ℝ)
    (hn : 0 < n) (hz : 0 ≤ z) (hsize : (n : ℝ) < z ^ 3) (hD : 1 ≤ D)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n ∧ z ≤ (p : ℝ))
    (hT : ∀ p ∈ S, ∀ d ∈ T p, (d : ℝ) < 2 * D)
    (hf : ∀ p ∈ S, ∀ d ∈ T p, ‖f p d‖ ≤ 1) :
    ‖∑ p ∈ S, ∑ d ∈ T p, f p d‖ ≤ 6 * D := by
  have hc : S.card ≤ 2 := prime_divisor_card_le_two S n z hn hz hsize hS
  have hi : ∀ p ∈ S, ‖∑ d ∈ T p, f p d‖ ≤ 3 * D := by
    intro p hp
    have hsub : T p ⊆ Finset.range (⌊2 * D⌋₊ + 1) := by
      intro d hd
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hT p hp d hd).le))
    have hcT : ((T p).card : ℝ) ≤ 3 * D := by
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range] at hcard
      have hfloor := Nat.floor_le (by linarith : 0 ≤ 2 * D)
      have hcard' : ((T p).card : ℝ) ≤ (⌊2 * D⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
      linarith
    calc
      _ ≤ ∑ d ∈ T p, ‖f p d‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ T p, (1 : ℝ) := Finset.sum_le_sum (hf p hp)
      _ = ((T p).card : ℝ) := by simp
      _ ≤ 3 * D := hcT
  calc
    _ ≤ ∑ p ∈ S, ‖∑ d ∈ T p, f p d‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, 3 * D := Finset.sum_le_sum hi
    _ = (S.card : ℝ) * (3 * D) := by simp [nsmul_eq_mul]
    _ ≤ 2 * (3 * D) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by linarith)
    _ = 6 * D := by ring

end LeanLab.KumchevLiu2007.Task687

#print axioms LeanLab.KumchevLiu2007.Task687.prime_divisor_card_le_two
#print axioms LeanLab.KumchevLiu2007.Task687.small_divisor_block_norm_le
