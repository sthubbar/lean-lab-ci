/-
P0076 Lemma 5.4 display 5.5, pages 19 to 20. The full coprimality indicator.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveResidues

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A prime common to the modulus and W gives a nonzero period of the whole sieve weight. -/
theorem compositeSieveSum_zero_of_prime_dvd_W {q p : ℕ} [NeZero q]
    (hp : p.Prime) (hpq : p ∣ q) (W V b : ℤ) (hpW : (p : ℤ) ∣ W)
    (a : ℕ) (ha : a.Coprime q) : compositeSieveSum q W V b a = 0 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have ht0 : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq0 hpq) hp.pos
  have htq : q / p < q := Nat.div_lt_self hq0 hp.one_lt
  have ht : (q / p : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt ht0 htq
  have haunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  unfold compositeSieveSum
  apply weighted_character_sum_eq_zero_of_unit (a : ZMod q) (q / p) haunit ht
  intro x
  apply prod_congr rfl
  intro r _
  by_cases hr : (r : ℕ) = p
  · have hW0 : (W : ZMod r) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd W r).mpr
      simpa only [hr] using hpW
    simp only [localSieveWeight, hW0, zero_mul, zero_add]
  · have hrprime := Nat.prime_of_mem_primeFactors r.property
    have hrt : (r : ℕ) ∣ q / p := by
      have hrq : (r : ℕ) ∣ (q / p) * p := by
        simpa only [Nat.div_mul_cancel hpq] using Nat.dvd_of_mem_primeFactors r.property
      rcases hrprime.dvd_mul.mp hrq with h | h
      · exact h
      · exact (hr ((Nat.prime_dvd_prime_iff_eq hrprime hp).mp h)).elim
    have htzero : (q / p : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrt
    let π : ZMod q →+* ZMod r := ZMod.castHom (Nat.dvd_of_mem_primeFactors r.property) (ZMod r)
    have hπ : π (x + (q / p : ZMod q)) = π x + (q / p : ZMod r) := by
      rw [map_add, map_natCast]
    have hecast : ((x + (q / p : ZMod q)).val : ZMod r) = (x.val : ZMod r) + (q / p : ZMod r) := by
      simpa only [π, ZMod.castHom_apply, ZMod.cast_eq_val] using hπ
    rw [hecast, htzero, add_zero]

/-- Failure of coprimality of q and W forces the entire character sum to vanish. -/
theorem compositeSieveSum_zero_of_not_coprime (q : ℕ) [NeZero q] (W V b : ℤ)
    (a : ℕ) (ha : a.Coprime q) (hW : ¬ IsCoprime (q : ℤ) W) :
    compositeSieveSum q W V b a = 0 := by
  have hex : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (q : ℤ) ∧ (p : ℤ) ∣ W := by
    by_contra hc
    push_neg at hc
    exact hW (isCoprime_of_primes (fun p hp hpq hpW => hc p hp hpq hpW))
  obtain ⟨p, hp, hpq, hpW⟩ := hex
  exact compositeSieveSum_zero_of_prime_dvd_W hp (Int.natCast_dvd_natCast.mp hpq) W V b hpW a ha

/-- The complete inequality in display 5.5, valid without amenability or coprimality of V. -/
theorem lemma54_proved (q : ℕ) [NeZero q] (W V b : ℤ) (a : ℕ) (ha : a.Coprime q) :
    ‖integerSieveSum q W V b a‖ ≤ (q.divisors.card : ℝ) *
      (if IsCoprime (q : ℤ) W then 1 else 0) := by
  by_cases hW : IsCoprime (q : ℤ) W
  · rw [if_pos hW, mul_one]
    exact integerSieveSum_norm_le_divisors q W V b a ha
  · rw [if_neg hW, mul_zero, ← compositeSieveSum_eq_integer,
      compositeSieveSum_zero_of_not_coprime q W V b a ha hW, norm_zero]

example : ‖integerSieveSum 15 3 1 1 1‖ = 0 := by
  have h := lemma54_proved 15 3 1 1 1 (by decide)
  norm_num [Int.isCoprime_iff_gcd_eq_one] at h
  rw [h, norm_zero]

#print axioms compositeSieveSum_zero_of_prime_dvd_W
#print axioms compositeSieveSum_zero_of_not_coprime
#print axioms lemma54_proved

end LeanLab.Teravainen2016
