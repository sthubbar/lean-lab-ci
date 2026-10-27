/-
R-0029, PC 20261020T1603Z-26078, unit U-1244, track T3.
Rigidity of representation functions and the parity of the Goldbach count.
AI wrote this Lean code. KNOWN mathematics, Dirac 1951 and folklore; nothing is claimed new.
Goldbach is OPEN; nothing here is progress on it.

Plain math twins:
* `rep A n` is the ordered count #{a ≤ n : a ∈ A, n - a ∈ A}.
* `rep_eq`: rep A n = 2 * #{a ∈ S : 2a < n} + [n even and n/2 ∈ A], the pairing a ↦ n - a.
* `rep_mod_two`: rep A n is odd iff n is even and n/2 ∈ A.
* `not_eventually_const`: no set A has rep A n = c > 0 for every n ≥ n0, Dirac's rigidity.
* `goldbach_rep_odd_iff`: the ordered Goldbach count of 2m is odd iff m is prime.
* `goldbach_iff_rep_pos`: 2m is a sum of two primes iff rep P (2m) > 0.
-/
import Mathlib

namespace LeanLab.Routes.R0029

open Finset

/-- Ordered representation count of `n` as `a + (n - a)` with both parts in `A`. -/
def rep (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

section General

variable (A : Set ℕ) [DecidablePred (· ∈ A)]

/-- the support set of `rep A n` -/
abbrev S (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)

lemma card_lt_eq_card_gt (n : ℕ) :
    ((S A n).filter (fun a => 2 * a < n)).card = ((S A n).filter (fun a => n < 2 * a)).card := by
  apply Finset.card_nbij' (fun a => n - a) (fun a => n - a)
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ha
    have e : n - (n - a) = a := by omega
    refine ⟨⟨by omega, h3, by rw [e]; exact h2⟩, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ha
    have e : n - (n - a) = a := by omega
    refine ⟨⟨by omega, h3, by rw [e]; exact h2⟩, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_range] at ha
    show n - (n - a) = a
    omega
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_range] at ha
    show n - (n - a) = a
    omega

lemma card_eq_mid (n : ℕ) :
    ((S A n).filter (fun a => 2 * a = n)).card = if (Even n ∧ n / 2 ∈ A) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨⟨k, hk⟩, hA⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨n / 2, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h2⟩; omega
    · rintro rfl
      have e : n - n / 2 = n / 2 := by omega
      exact ⟨⟨by omega, hA, by rw [e]; exact hA⟩, by omega⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha h2
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    apply h
    have e : n / 2 = a := by omega
    exact ⟨⟨a, by omega⟩, by rw [e]; exact ha.2.1⟩

/-- `rep A n = 2 * #{a : 2a < n} + [n even, n/2 ∈ A]` -/
theorem rep_eq (n : ℕ) :
    rep A n = 2 * ((S A n).filter (fun a => 2 * a < n)).card
      + (if (Even n ∧ n / 2 ∈ A) then 1 else 0) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := S A n) (p := fun a => 2 * a < n)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (S A n).filter (fun a => ¬ 2 * a < n)) (p := fun a => 2 * a = n)
  have e1 : ((S A n).filter (fun a => ¬ 2 * a < n)).filter (fun a => 2 * a = n)
      = (S A n).filter (fun a => 2 * a = n) := by
    ext a; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, by omega⟩, h'⟩
  have e2 : ((S A n).filter (fun a => ¬ 2 * a < n)).filter (fun a => ¬ 2 * a = n)
      = (S A n).filter (fun a => n < 2 * a) := by
    ext a; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, by omega⟩, by omega⟩
  rw [e1, e2] at h2
  rw [← card_eq_mid A n, two_mul]
  have h3 := card_lt_eq_card_gt A n
  show (S A n).card = _
  omega

/-- the parity of an ordered representation count -/
theorem rep_mod_two (n : ℕ) :
    rep A n % 2 = if (Even n ∧ n / 2 ∈ A) then 1 else 0 := by
  rw [rep_eq]; split_ifs <;> omega

lemma rep_ge_of_Icc (n n0 : ℕ) (hA : ∀ m ≥ n0, m ∈ A) (hn : 2 * n0 ≤ n) :
    n + 1 - 2 * n0 ≤ rep A n := by
  have hsub : Finset.Icc n0 (n - n0) ⊆ S A n := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hA a ha.1, hA _ (by omega)⟩
  have := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at this
  have hr : rep A n = (S A n).card := rfl
  rw [hr]; omega

/-- Dirac's rigidity: no ordered representation function is eventually a positive constant. -/
theorem not_eventually_const (c n0 : ℕ) (hc : 0 < c) (h : ∀ n ≥ n0, rep A n = c) : False := by
  have par : ∀ m ≥ n0, (if m ∈ A then 1 else 0) = c % 2 := by
    intro m hm
    have h1 := rep_mod_two A (2 * m)
    rw [h (2 * m) (by omega)] at h1
    have he : Even (2 * m) := even_two_mul m
    have hd : 2 * m / 2 = m := by omega
    simp only [he, hd, true_and] at h1
    omega
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · -- no large element lies in A, so rep vanishes at 2 n0 + 2
    have hA : ∀ m ≥ n0, m ∉ A := by
      intro m hm hmA
      have := par m hm; simp [hmA] at this; omega
    have hz : rep A (2 * n0 + 2) = 0 := by
      unfold rep
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha ⟨haA, hbA⟩
      simp only [Finset.mem_range] at ha
      by_cases hlt : a < n0
      · exact hA _ (by omega) hbA
      · exact hA a (by omega) haA
    have := h (2 * n0 + 2) (by omega); omega
  · -- every large m lies in A, so rep grows
    have hA : ∀ m ≥ n0, m ∈ A := by
      intro m hm
      by_contra hmA
      have := par m hm; simp [hmA] at this; omega
    have hge := rep_ge_of_Icc A (2 * n0 + c) n0 hA (by omega)
    have := h (2 * n0 + c) (by omega)
    omega

end General

/-- the primes as a set -/
abbrev Pr : Set ℕ := {p | p.Prime}

instance : DecidablePred (· ∈ Pr) := fun p => Nat.decidablePrime p

/-- the ordered Goldbach count of `2m` is odd iff `m` is prime -/
theorem goldbach_rep_odd_iff (m : ℕ) : rep Pr (2 * m) % 2 = 1 ↔ m.Prime := by
  rw [rep_mod_two]
  have he : Even (2 * m) := even_two_mul m
  have hd : 2 * m / 2 = m := by omega
  simp only [he, hd, true_and]
  split_ifs with h
  · simpa using h
  · simp only [Set.mem_ofPred_eq] at h; simp [h]

/-- `n` is a sum of two primes iff the ordered Goldbach count of `n` is positive -/
theorem goldbach_iff_rep_pos (n : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) ↔ 0 < rep Pr n := by
  unfold rep
  rw [Finset.card_pos]
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨by omega, hp, ?_⟩
    rw [Nat.add_sub_cancel_left]; exact hq
  · rintro ⟨a, ha⟩
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
    exact ⟨a, n - a, ha.2.1, ha.2.2, by omega⟩

/-- for composite `m` the count of `2m` is even, so parity says nothing about positivity -/
theorem rep_even_of_not_prime (m : ℕ) (hm : ¬ m.Prime) : rep Pr (2 * m) % 2 = 0 := by
  have := (goldbach_rep_odd_iff m).not.mpr hm
  omega

/-- vacuity: 10 = 3 + 7 = 5 + 5 = 7 + 3, three ordered pairs, odd, and 5 is prime -/
theorem vacuity_10 : rep Pr 10 = 3 := by decide

/-- vacuity: 12 = 5 + 7 = 7 + 5, even, and 6 is not prime -/
theorem vacuity_12 : rep Pr 12 = 2 := by decide

/-- the primes are not eventually a constant-count basis -/
theorem primes_not_const (c n0 : ℕ) (hc : 0 < c) : ¬ ∀ n ≥ n0, rep Pr n = c :=
  fun h => not_eventually_const Pr c n0 hc h

end LeanLab.Routes.R0029
