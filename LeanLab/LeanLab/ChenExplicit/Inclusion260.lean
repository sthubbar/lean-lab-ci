/-
AI wrote the Lean code. Codex task260, 2026-11-04.
Finite inclusion and exclusion for Yamada 2015 arXiv 1511.03409v2
page 13 Lemma 5.2 eq 57. The finite distinguished divisors are distinct
members of the sieving set. Primality is not needed for this counting identity.
The analytic lower sieve estimate remains open. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.Inclusion260

/-- The number of members of A avoiding every divisor in P. -/
def siftCount (A P : Finset ℕ) : ℕ :=
  (A.filter (fun a => ∀ p ∈ P, ¬ p ∣ a)).card

/-- Members of A divisible by every distinguished divisor before index i. -/
def divPrefix (A : Finset ℕ) (q : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  A.filter (fun a => ∀ j ∈ range i, q j ∣ a)

/-- The sieving divisors after removing the first i distinguished divisors. -/
def sieveTail (P : Finset ℕ) (q : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  P \ (range i).image q

/-- The one step partition in the proof of Yamada page 13 Lemma 5.2. -/
theorem sift_count_partition (A P : Finset ℕ) (p : ℕ) (hp : p ∈ P) :
    siftCount A P + siftCount (A.filter (fun a => p ∣ a)) (P.erase p) =
      siftCount A (P.erase p) := by
  let S := A.filter (fun a => ∀ r ∈ P.erase p, ¬ r ∣ a)
  have heq : A.filter (fun a => ∀ r ∈ P, ¬ r ∣ a) = S.filter (fun a => ¬ p ∣ a) := by
    ext a
    simp only [S, mem_filter]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨⟨ha, fun r hr => h r (mem_of_mem_erase hr)⟩, h p hp⟩
    · rintro ⟨⟨ha, h⟩, hp'⟩
      refine ⟨ha, fun r hr => ?_⟩
      by_cases he : r = p
      · simpa only [he] using hp'
      · exact h r (mem_erase.mpr ⟨he, hr⟩)
  have heq' : (A.filter (fun a => p ∣ a)).filter (fun a => ∀ r ∈ P.erase p, ¬ r ∣ a) =
      S.filter (fun a => p ∣ a) := by
    ext a
    simp only [S, mem_filter]
    tauto
  unfold siftCount
  rw [heq, heq', add_comm]
  exact card_filter_add_card_filter_not (s := S) (fun a => p ∣ a)

/-- Adding the next distinguished divisor to the divisibility prefix. -/
theorem divPrefix_succ (A : Finset ℕ) (q : ℕ → ℕ) (i : ℕ) :
    divPrefix A q (i + 1) = (divPrefix A q i).filter (fun a => q i ∣ a) := by
  ext a
  simp only [divPrefix, mem_filter, mem_range]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, fun j hj => h j (by omega)⟩, h i (by omega)⟩
  · rintro ⟨⟨ha, h⟩, hi⟩
    refine ⟨ha, fun j hj => ?_⟩
    rcases lt_or_eq_of_le (show j ≤ i by omega) with hj' | rfl
    · exact h j hj'
    · exact hi

/-- Removing the next distinguished divisor from the sieving tail. -/
theorem sieveTail_succ (P : Finset ℕ) (q : ℕ → ℕ) (i : ℕ) :
    sieveTail P q (i + 1) = (sieveTail P q i).erase (q i) := by
  ext p
  simp only [sieveTail, range_add_one, image_insert, mem_sdiff, mem_insert, mem_erase]
  tauto

/-- For distinct prime divisors the prefix is divisibility by their product.
This connects the finite count with A superscript i on Yamada page 11. -/
theorem divPrefix_eq_product_filter (A : Finset ℕ) (q : ℕ → ℕ) (i : ℕ)
    (hq : ∀ j < i, (q j).Prime) (hinj : Set.InjOn q (↑(range i) : Set ℕ)) :
    divPrefix A q i = A.filter (fun a => (∏ j ∈ range i, q j) ∣ a) := by
  have hcop : (↑(range i) : Set ℕ).Pairwise (fun j k => IsCoprime (q j : ℤ) (q k : ℤ)) := by
    intro j hj k hk hjk
    apply Nat.isCoprime_iff_coprime.mpr
    apply (Nat.coprime_primes (hq j (mem_range.mp hj)) (hq k (mem_range.mp hk))).mpr
    intro h
    exact hjk (hinj hj hk h)
  ext a
  simp only [divPrefix, mem_filter]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    have hprod : (∏ j ∈ range i, (q j : ℤ)) ∣ (a : ℤ) :=
      Finset.prod_dvd_of_coprime hcop (fun j hj => by exact_mod_cast h j hj)
    exact_mod_cast hprod
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun j hj => (dvd_prod_of_mem q hj).trans h⟩

/-- The finite form of Yamada page 13 Lemma 5.2 eq 57.
The explicit hypotheses make every one step sieve partition valid. -/
theorem lemma52_finite (A P : Finset ℕ) (q : ℕ → ℕ) (l : ℕ)
    (hmem : ∀ i < l, q i ∈ P) (hinj : Set.InjOn q (↑(range l) : Set ℕ)) :
    (siftCount A P : ℤ) =
      (∑ i ∈ range l, (-1 : ℤ) ^ i *
        (siftCount (divPrefix A q i) (sieveTail P q (i + 1)) : ℤ)) +
      (-1 : ℤ) ^ l * (siftCount (divPrefix A q l) (sieveTail P q l) : ℤ) := by
  let F : ℕ → ℤ := fun i => (siftCount (divPrefix A q i) (sieveTail P q i) : ℤ)
  let G : ℕ → ℤ := fun i => (siftCount (divPrefix A q i) (sieveTail P q (i + 1)) : ℤ)
  have hp (i : ℕ) (hi : i < l) : q i ∈ sieveTail P q i := by
    apply mem_sdiff.mpr
    refine ⟨hmem i hi, ?_⟩
    intro h
    obtain ⟨j, hj, he⟩ := mem_image.mp h
    have hj' : j < i := mem_range.mp hj
    have he' : j = i := hinj (mem_range.mpr (by omega)) (mem_range.mpr hi) he
    omega
  have hstep (i : ℕ) (hi : i < l) : F i + F (i + 1) = G i := by
    have h := sift_count_partition (divPrefix A q i) (sieveTail P q i) (q i) (hp i hi)
    rw [← divPrefix_succ, ← sieveTail_succ] at h
    dsimp [F, G]
    exact_mod_cast h
  have heq (i : ℕ) (hi : i ∈ range l) :
      (-1 : ℤ) ^ i * G i = (-1 : ℤ) ^ i * F i - (-1 : ℤ) ^ (i + 1) * F (i + 1) := by
    rw [← hstep i (mem_range.mp hi), pow_succ]
    ring
  have hsum := sum_range_sub' (fun i => (-1 : ℤ) ^ i * F i) l
  have hsum' : (∑ i ∈ range l, (-1 : ℤ) ^ i * G i) = F 0 - (-1 : ℤ) ^ l * F l := by
    calc
      _ = ∑ i ∈ range l, ((-1 : ℤ) ^ i * F i - (-1 : ℤ) ^ (i + 1) * F (i + 1)) :=
        sum_congr rfl heq
      _ = _ := by simpa using hsum
  have hF0 : F 0 = (siftCount A P : ℤ) := by simp [F, divPrefix, sieveTail]
  change (siftCount A P : ℤ) = (∑ i ∈ range l, (-1 : ℤ) ^ i * G i) + (-1 : ℤ) ^ l * F l
  rw [hsum', hF0]
  ring

/-- Yamada page 13 Lemma 5.2 in the paper product divisibility notation.
The distinguished primes are distinct members of the finite sieving set. -/
theorem lemma52_prime_products (A P : Finset ℕ) (q : ℕ → ℕ) (l : ℕ)
    (hmem : ∀ i < l, q i ∈ P) (hq : ∀ i < l, (q i).Prime)
    (hinj : Set.InjOn q (↑(range l) : Set ℕ)) :
    (siftCount A P : ℤ) =
      (∑ i ∈ range l, (-1 : ℤ) ^ i *
        (siftCount (A.filter (fun a => (∏ j ∈ range i, q j) ∣ a))
          (sieveTail P q (i + 1)) : ℤ)) +
      (-1 : ℤ) ^ l * (siftCount (A.filter (fun a => (∏ j ∈ range l, q j) ∣ a))
        (sieveTail P q l) : ℤ) := by
  have hpref (i : ℕ) (hi : i ≤ l) : divPrefix A q i =
      A.filter (fun a => (∏ j ∈ range i, q j) ∣ a) := by
    apply divPrefix_eq_product_filter
    · intro j hj
      exact hq j (hj.trans_le hi)
    · intro j hj k hk he
      exact hinj (mem_range.mpr ((mem_range.mp hj).trans_le hi))
        (mem_range.mpr ((mem_range.mp hk).trans_le hi)) he
  rw [lemma52_finite A P q l hmem hinj]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [hpref i (mem_range.mp hi).le]
  · rw [hpref l le_rfl]

end LeanLab.ChenExplicit.Inclusion260
