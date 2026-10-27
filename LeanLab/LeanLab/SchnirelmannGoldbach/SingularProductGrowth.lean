/-
Elementary control of the singular product for Brun's page 127 ratio consequence.
This is a lab derivation, not Brun's printed logarithmic estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.S1.Final

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach

/-- There are at most a divided by 2 minus 1 odd integers at least 3 below odd a. -/
theorem odd_card_below (S : Finset ℕ) (hS : ∀ p ∈ S, 3 ≤ p ∧ Odd p)
    (a : ℕ) (ha : 3 ≤ a ∧ Odd a) (hlt : ∀ p ∈ S, p < a) :
    2 * S.card + 3 ≤ a := by
  have hinj : Set.InjOn (fun p : ℕ => p / 2) (S : Set ℕ) := by
    intro p hp q hq hpq
    change p / 2 = q / 2 at hpq
    have hpodd := Nat.odd_iff.mp (hS p hp).2
    have hqodd := Nat.odd_iff.mp (hS q hq).2
    omega
  have hsub : S.image (fun p => p / 2) ⊆ Ioo 0 (a / 2) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    have hp3 := (hS p hp).1
    have hpodd := Nat.odd_iff.mp (hS p hp).2
    have haodd := Nat.odd_iff.mp ha.2
    have hpa := hlt p hp
    simp only [mem_Ioo]
    omega
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  simp only [Nat.card_Ioo] at hc
  have haodd := Nat.odd_iff.mp ha.2
  omega

/-- Odd spacing gives a square-root bound for the product over any such set. -/
theorem odd_product_sq_le_card (S : Finset ℕ) (hS : ∀ p ∈ S, 3 ≤ p ∧ Odd p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) ^ 2 ≤ (S.card : ℝ) + 1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    have ha := hS a (mem_insert_self a S)
    have hS' : ∀ p ∈ S, 3 ≤ p ∧ Odd p := fun p hp => hS p (mem_insert_of_mem hp)
    have ih' := ih hS'
    have hrank := odd_card_below S hS' a ha hlt
    have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have hrankR : 2 * (S.card : ℝ) + 3 ≤ a := by exact_mod_cast hrank
    have hlocal : (1 + 1 / (a : ℝ)) ^ 2 * ((S.card : ℝ) + 1) ≤ (S.card : ℝ) + 2 := by
      rw [show (1 + 1 / (a : ℝ)) = ((a : ℝ) + 1) / a by field_simp,
        div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have hmul := mul_le_mul_of_nonneg_right hrankR haR.le
      have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      nlinarith
    rw [prod_insert haS, mul_pow, card_insert_of_notMem haS]
    push_cast
    calc (1 + 1 / (a : ℝ)) ^ 2 * (∏ p ∈ S, (1 + 1 / (p : ℝ))) ^ 2
        ≤ (1 + 1 / (a : ℝ)) ^ 2 * ((S.card : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ih' (sq_nonneg _)
      _ ≤ (S.card : ℝ) + 1 + 1 := by linarith

/-- Separating the prime 2 gives an explicit bound for every singular product square. -/
theorem singProd_sq_le_card (n : ℕ) :
    singProd n ^ 2 ≤ (9 / 4 : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
  let S := n.primeFactors.erase 2
  have hS : ∀ p ∈ S, 3 ≤ p ∧ Odd p := by
    intro p hp
    obtain ⟨hp2, hp⟩ := mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hodd := (hprime.eq_two_or_odd').resolve_left hp2
    exact ⟨by have := hprime.two_le; omega, hodd⟩
  have hodd := odd_product_sq_le_card S hS
  have hcard : (S.card : ℝ) ≤ n.primeFactors.card := by
    exact_mod_cast card_le_card (erase_subset 2 n.primeFactors)
  by_cases h2 : 2 ∈ n.primeFactors
  · have heq : singProd n = (3 / 2 : ℝ) * ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
      unfold singProd
      rw [← mul_prod_erase n.primeFactors (fun p => (1 + 1 / (p : ℝ))) h2]
      norm_num [S]
    rw [heq, mul_pow]
    nlinarith
  · have heq : S = n.primeFactors := erase_eq_of_notMem h2
    rw [heq] at hodd
    unfold singProd
    have hc : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
    nlinarith

/-- The singular product square is at most 9 times log n for n at least 3. -/
theorem singProd_sq_le_log (n : ℕ) (hn : 3 ≤ n) :
    singProd n ^ 2 ≤ 9 * Real.log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by
    have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 : ∏ p ∈ n.primeFactors, p ≤ n :=
      Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    exact_mod_cast h1.trans h2
  have hω := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hω
  have hω0 : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
  have hω2 : (n.primeFactors.card : ℝ) ≤ 2 * Real.log n := by
    nlinarith [Real.log_two_gt_d9]
  have hlog : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < n)).mpr
      (Real.exp_one_lt_three.le.trans hnR)
  have hsp := singProd_sq_le_card n
  nlinarith

end LeanLab.SchnirelmannGoldbach

#print axioms LeanLab.SchnirelmannGoldbach.odd_card_below

#print axioms LeanLab.SchnirelmannGoldbach.odd_product_sq_le_card

#print axioms LeanLab.SchnirelmannGoldbach.singProd_sq_le_card

#print axioms LeanLab.SchnirelmannGoldbach.singProd_sq_le_log
