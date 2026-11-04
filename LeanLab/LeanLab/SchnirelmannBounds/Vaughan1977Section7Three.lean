/-
Vaughan 1977 page 107, the modulus 3 contribution in equation 7.4.
https://doi.org/10.1515/crll.1977.290.93
This file handles the intervals that exclude the prime 3.
The full weighted lower bound and its asymptotics remain open.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Section7

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Section7Three
open Vaughan1977Section7

/-- The two nonzero residue classes give the sharp ordered pair bound modulo 3. -/
theorem pair_count_mod_three (P : Finset ℕ) (hP : ∀ p ∈ P, p % 3 ≠ 0) :
    2 * ((P ×ˢ P).filter (fun pq => 3 ∣ pq.1 + pq.2)).card ≤ P.card^2 := by
  let A := P.filter (fun p => p % 3 = 1)
  let B := P.filter (fun p => p % 3 = 2)
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have h1 := (mem_filter.mp hp).2
    have h2 := (mem_filter.mp hq).2
    omega
  have hu : A ∪ B = P := by
    ext p
    simp only [A, B, mem_union, mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have h0 := hP p hp
      have h3 := Nat.mod_lt p (by norm_num : 0 < 3)
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  have hpair : (P ×ˢ P).filter (fun pq => 3 ∣ pq.1 + pq.2) = (A ×ˢ B) ∪ (B ×ˢ A) := by
    ext pq
    simp only [A, B, mem_filter, mem_product, mem_union]
    constructor
    · rintro ⟨⟨hp, hq⟩, hdvd⟩
      have h1 := hP pq.1 hp
      have h2 := hP pq.2 hq
      have h13 := Nat.mod_lt pq.1 (by norm_num : 0 < 3)
      have h23 := Nat.mod_lt pq.2 (by norm_num : 0 < 3)
      have hmod := Nat.mod_eq_zero_of_dvd hdvd
      rw [Nat.add_mod] at hmod
      rcases (show (pq.1 % 3 = 1 ∧ pq.2 % 3 = 2) ∨
          (pq.1 % 3 = 2 ∧ pq.2 % 3 = 1) by omega) with h | h
      · exact Or.inl ⟨⟨hp, h.1⟩, ⟨hq, h.2⟩⟩
      · exact Or.inr ⟨⟨hp, h.1⟩, ⟨hq, h.2⟩⟩
    · rintro (⟨⟨hp, h1⟩, ⟨hq, h2⟩⟩ | ⟨⟨hp, h1⟩, ⟨hq, h2⟩⟩)
      · refine ⟨⟨hp, hq⟩, Nat.dvd_of_mod_eq_zero ?_⟩
        rw [Nat.add_mod, h1, h2]
      · refine ⟨⟨hp, hq⟩, Nat.dvd_of_mod_eq_zero ?_⟩
        rw [Nat.add_mod, h1, h2]
  have hprod : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    rw [Finset.disjoint_left]
    intro pq hp hq
    exact (Finset.disjoint_left.mp hd) (mem_product.mp hp).1 (mem_product.mp hq).1
  have hc : A.card + B.card = P.card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  rw [hpair, Finset.card_union_of_disjoint hprod, Finset.card_product, Finset.card_product, ← hc]
  nlinarith [four_mul_le_sq_add A.card B.card]

/-- The restricted representation sum is the corresponding count of ordered pairs. -/
theorem Rk_three_fibres (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∑ n ∈ (Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊).filter (fun n => 3 ∣ n), Rk x k n =
      (((intervalPrimes x k) ×ˢ (intervalPrimes x k)).filter
        (fun pq => 3 ∣ pq.1 + pq.2)).card := by
  let P := intervalPrimes x k
  let J := (Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊).filter (fun n => 3 ∣ n)
  have hmaps : ∀ pq ∈ P ×ˢ P, pq.1 + pq.2 ∈ Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊ := by
    intro pq hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hp3, _, _, hpu⟩ := (mem_intervalPrimes hx).mp hp
    obtain ⟨hq3, _, _, hqu⟩ := (mem_intervalPrimes hx).mp hq
    refine mem_Icc.mpr ⟨by omega, Nat.le_floor ?_⟩
    push_cast
    linarith
  have hf : (P ×ˢ P).filter (fun pq => pq.1 + pq.2 ∈ J) =
      (P ×ˢ P).filter (fun pq => 3 ∣ pq.1 + pq.2) := by
    ext pq
    simp only [mem_filter]
    constructor
    · rintro ⟨hpq, hJ⟩
      exact ⟨hpq, (mem_filter.mp hJ).2⟩
    · rintro ⟨hpq, hdvd⟩
      exact ⟨hpq, mem_filter.mpr ⟨hmaps pq hpq, hdvd⟩⟩
  change (∑ n ∈ J, ((P ×ˢ P).filter (fun pq => pq.1 + pq.2 = n)).card) = _
  rw [Finset.sum_card_fiberwise_eq_card_filter, hf]

/-- The modulus 3 term loses at most one quarter of the total mass when 3 is excluded. -/
theorem mod_three_loss (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hstart : 6 ≤ (k : ℝ) * x) :
    (3 / 4 : ℝ) * (intervalPrimes x k).card^2 ≤
      (intervalPrimes x k).card^2 - (1 / 2 : ℝ) *
        (∑ n ∈ (Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊).filter (fun n => 3 ∣ n), Rk x k n : ℕ) := by
  have hnz : ∀ p ∈ intervalPrimes x k, p % 3 ≠ 0 := by
    intro p hp hmod
    obtain ⟨hp3, hpp, hpl, _⟩ := (mem_intervalPrimes hx).mp hp
    have hpR : (3 : ℝ) < p := by linarith
    have hpgt : 3 < p := by exact_mod_cast hpR
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp (Nat.dvd_of_mod_eq_zero hmod)
    omega
  have h := pair_count_mod_three (intervalPrimes x k) hnz
  rw [← Rk_three_fibres x hx k] at h
  have hr : (2 : ℝ) *
      (∑ n ∈ (Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊).filter (fun n => 3 ∣ n), Rk x k n : ℕ) ≤
      ((intervalPrimes x k).card : ℝ)^2 := by exact_mod_cast h
  nlinarith

example : ∀ p ∈ ({5, 7} : Finset ℕ), p % 3 ≠ 0 := by decide
example : 2 * ((({5, 7} : Finset ℕ) ×ˢ {5, 7}).filter
    (fun pq => 3 ∣ pq.1 + pq.2)).card = ({5, 7} : Finset ℕ).card^2 := by decide
example : (0 : ℝ) ≤ 4 ∧ (6 : ℝ) ≤ (2 : ℕ) * (4 : ℝ) := by norm_num

end LeanLab.SchnirelmannBounds.Vaughan1977Section7Three

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7Three.pair_count_mod_three

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7Three.Rk_three_fibres

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7Three.mod_three_loss
