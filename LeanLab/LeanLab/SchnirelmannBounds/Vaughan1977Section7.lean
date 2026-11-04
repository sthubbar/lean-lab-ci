/-
Vaughan 1977 page 106, equations 7.1 and 7.2.
https://doi.org/10.1515/crll.1977.290.93
Elementary counting identities from the alternative argument.
The asymptotic estimates of Section 7 remain unformalized.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma3

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Section7

/-- The two residue classes in equation 7.1 satisfy its identity and upper bound. -/
theorem equation71 (x : ℝ) :
    4 * (Vaughan1977Lemma3.pi_interval x 0 3 1 : ℝ) *
        (Vaughan1977Lemma3.pi_interval x 0 3 2 : ℝ) =
      ((Vaughan1977Lemma3.pi_interval x 0 3 1 : ℝ) +
        (Vaughan1977Lemma3.pi_interval x 0 3 2 : ℝ))^2 -
      ((Vaughan1977Lemma3.pi_interval x 0 3 1 : ℝ) -
        (Vaughan1977Lemma3.pi_interval x 0 3 2 : ℝ))^2 ∧
    4 * (Vaughan1977Lemma3.pi_interval x 0 3 1 : ℝ) *
        (Vaughan1977Lemma3.pi_interval x 0 3 2 : ℝ) ≤
      (Nat.primeCounting ⌊x⌋₊ : ℝ)^2 := by
  let A := (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ 1 [MOD 3])
  let B := (Ioc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p ≡ 2 [MOD 3])
  simp only [Vaughan1977Lemma3.pi_interval, add_zero, Nat.floor_zero]
  change 4 * (A.card : ℝ) * B.card = ((A.card : ℝ) + B.card)^2 -
      ((A.card : ℝ) - B.card)^2 ∧
    4 * (A.card : ℝ) * B.card ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)^2
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have h1 := (mem_filter.mp hp).2.2
    have h2 := (mem_filter.mp hq).2.2
    change p % 3 = 1 at h1
    change p % 3 = 2 at h2
    omega
  have hsub : A ∪ B ⊆ (⌊x⌋₊).primesLE := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2.1⟩
    · exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2.1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Nat.primesLE_card_eq_primeCounting] at hc
  have hr : (A.card : ℝ) + B.card ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by exact_mod_cast hc
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (A.card : ℝ) + B.card) hr 2
  constructor
  · ring
  · exact (four_mul_le_sq_add (A.card : ℝ) (B.card : ℝ)).trans hs

/-- The odd primes in the common interval used in equation 7.2. -/
def intervalPrimes (x : ℝ) (k : ℕ) : Finset ℕ :=
  (Icc 3 ⌊(k : ℝ) * x / 2 + x⌋₊).filter
    (fun p => p.Prime ∧ (k : ℝ) * x / 2 < (p : ℝ))

/-- The ordered representation count of equation 7.2. -/
def Rk (x : ℝ) (k n : ℕ) : ℕ :=
  (((intervalPrimes x k) ×ˢ (intervalPrimes x k)).filter (fun pq => pq.1 + pq.2 = n)).card

/-- Exact real interval membership for the set in equation 7.2. -/
theorem mem_intervalPrimes {x : ℝ} (hx : 0 ≤ x) {k p : ℕ} :
    p ∈ intervalPrimes x k ↔
      3 ≤ p ∧ p.Prime ∧ (k : ℝ) * x / 2 < (p : ℝ) ∧ (p : ℝ) ≤ (k : ℝ) * x / 2 + x := by
  have hu : 0 ≤ (k : ℝ) * x / 2 + x := by positivity
  simp only [intervalPrimes, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hp3, hpu⟩, hpr, hpl⟩
    have hc : (p : ℝ) ≤ ⌊(k : ℝ) * x / 2 + x⌋₊ := by exact_mod_cast hpu
    exact ⟨hp3, hpr, hpl, hc.trans (Nat.floor_le hu)⟩
  · rintro ⟨hp3, hpr, hpl, hpu⟩
    exact ⟨⟨hp3, Nat.le_floor hpu⟩, hpr, hpl⟩

/-- A positive representation count has the parity and support stated in Section 7. -/
theorem Rk_support {x : ℝ} (hx : 0 ≤ x) {k n : ℕ} (hn : 0 < Rk x k n) :
    Even n ∧ (k : ℝ) * x < (n : ℝ) ∧ (n : ℝ) ≤ (k : ℝ) * x + 2 * x := by
  obtain ⟨⟨p, q⟩, hpq⟩ := Finset.card_pos.mp hn
  obtain ⟨hpq, he⟩ := mem_filter.mp hpq
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  obtain ⟨hp3, hpp, hpl, hpu⟩ := (mem_intervalPrimes hx).mp hp
  obtain ⟨hq3, hqp, hql, hqu⟩ := (mem_intervalPrimes hx).mp hq
  subst n
  refine ⟨(hpp.odd_of_ne_two (by omega)).add_odd (hqp.odd_of_ne_two (by omega)), ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- Summing the representation fibres gives the square of the interval prime count. -/
theorem sum_Rk (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∑ n ∈ Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊, Rk x k n = (intervalPrimes x k).card^2 := by
  have hmaps : ∀ pq ∈ (intervalPrimes x k) ×ˢ (intervalPrimes x k),
      pq.1 + pq.2 ∈ Icc 1 ⌊(k : ℝ) * x + 2 * x⌋₊ := by
    intro pq hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hp3, hpp, hpl, hpu⟩ := (mem_intervalPrimes hx).mp hp
    obtain ⟨hq3, hqp, hql, hqu⟩ := (mem_intervalPrimes hx).mp hq
    refine mem_Icc.mpr ⟨by omega, Nat.le_floor ?_⟩
    push_cast
    linarith
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa only [Finset.card_product, Rk, pow_two] using h.symm

example : intervalPrimes 5 0 = {3, 5} := by
  have h : Icc (3 : ℕ) 5 = {3, 4, 5} := by decide
  norm_num [intervalPrimes, h, Finset.filter_insert, Finset.filter_singleton]

example : Rk 5 0 6 = 1 ∧ Rk 5 0 8 = 2 ∧ Rk 5 0 10 = 1 := by
  have h : Icc (3 : ℕ) 5 = {3, 4, 5} := by decide
  have hs : intervalPrimes 5 0 = {3, 5} := by
    norm_num [intervalPrimes, h, Finset.filter_insert, Finset.filter_singleton]
  simp only [Rk, hs]
  decide

end LeanLab.SchnirelmannBounds.Vaughan1977Section7

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7.equation71

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7.mem_intervalPrimes

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7.Rk_support

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Section7.sum_Rk
