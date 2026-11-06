import LeanLab.Ricci1937.Decomp338l

/-!
Ricci 1937, finite mixed W count supplier.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary prime product divisibility for second memoir pages 106 and 107.
Distinct prime factors divide an integer jointly exactly when each divides it. -/
lemma decomp338_prime_product_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro hd p hp
    exact (dvd_prod_of_mem id hp).trans hd
  · intro hd
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
    · exact hd

/-- Auxiliary selected prime divisibility for second memoir pages 106 and 107.
Inside a finite prime set, divisibility of its selected prime product records exactly the selection predicate. -/
lemma decomp338_filtered_prime_product_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : ℕ → Prop) [DecidablePred Q] (p : ℕ) (hp : p ∈ P) :
    p ∣ (∏ q ∈ P.filter Q, q) ↔ Q p := by
  rw [(Nat.prime_iff.mp (hP p hp)).dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hd⟩
    have heq := (Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q (mem_filter.mp hq).1)).mp hd
    subst q
    exact (mem_filter.mp hq).2
  · intro hQ
    exact ⟨p, mem_filter.mpr ⟨hp, hQ⟩, dvd_refl p⟩

/-- Auxiliary integer encoding of the actual mixed W bad prime conditions.
Low primes divide both factor products and high primes divide the first factor.
Second memoir pages 106, 107 and 115. -/
def decomp338MixedWProduct (N v t x : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primesLE t).filter (fun p =>
    if p ≤ v then p ∣ x * (N - x) else p ∣ x), p

/-- Auxiliary exact mixed W discrepancy for second memoir pages 106, 107 and 115.
The actual low and high residue conditions have the encoded local density and root error. -/
lemma decomp338_mixed_W_remainder (N v t : ℕ) (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
    |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} : ℝ) -
      (N : ℝ) * ∏ p ∈ S, nuN (decomp338EncodedGap N v t) p| ≤
        cnt (decomp338EncodedGap N v t) (∏ p ∈ S, p) := by
  let H := decomp338EncodedGap N v t
  let A := S.filter (fun p => p ≤ v)
  let B := S.filter (fun p => v < p)
  let d := ∏ p ∈ A, p
  let e := ∏ p ∈ B, p
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hprimeA : ∀ p ∈ A, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hprimeB : ∀ p ∈ B, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hpv : p ≤ v
      · exact Or.inl ⟨hp, hpv⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hprod : (∏ p ∈ S, p) = d * e := by rw [hAB, prod_union hdisj]
  have hd : 0 < d := prod_pos (fun p hp => (hprimeA p hp).pos)
  have he : 0 < e := prod_pos (fun p hp => (hprimeB p hp).pos)
  have hcop : Nat.Coprime d e := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    apply (Nat.coprime_primes (hprimeA p hp) (hprimeB q hq)).mpr
    intro hpq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hlow (p : ℕ) (hp : p ∈ A) : wt H p = wt N p := by
    have hh := decomp338_encoded_gap_low N v t p (hprimeA p hp) (mem_filter.mp hp).2
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeA p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeA p hp)] using hh
  have hhigh (p : ℕ) (hp : p ∈ B) : wt H p = 1 := by
    have hpt := (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
    have hh := decomp338_encoded_gap_high N v t p (hprimeB p hp) (mem_filter.mp hp).2 hpt
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeB p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeB p hp)] using hh
  have hcnt : (cnt H (∏ p ∈ S, p) : ℝ) = cnt N d := by
    rw [cnt_prod_primes H S hprime, cnt_prod_primes N A hprimeA]
    calc
      _ = (∏ p ∈ A, wt H p) * ∏ p ∈ B, wt H p := by rw [hAB, prod_union hdisj]
      _ = (∏ p ∈ A, wt N p) * 1 := by
        rw [prod_congr rfl hlow, prod_eq_one hhigh]
      _ = _ := mul_one _
  have hdensity : (cnt H (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) = ∏ p ∈ S, nuN H p := by
    rw [cnt_prod_primes H S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN H p) = (cnt N d : ℝ) * N / (d * e) := by
    rw [← hdensity, hcnt, hprod, Nat.cast_mul]
    ring
  have hcount : #{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} =
      #{x ∈ range N | d ∣ x * (N - x) ∧ e ∣ x} := by
    congr 1
    apply filter_congr
    intro x hx
    have hcode (p : ℕ) (hp : p ∈ S) : p ∣ decomp338MixedWProduct N v t x ↔
        (if p ≤ v then p ∣ x * (N - x) else p ∣ x) :=
      decomp338_filtered_prime_product_dvd (Nat.primesLE t) hP _ p (hS hp)
    rw [decomp338_prime_product_dvd_iff S hprime,
      decomp338_prime_product_dvd_iff A hprimeA, decomp338_prime_product_dvd_iff B hprimeB]
    constructor
    · intro hall
      constructor
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_pos (mem_filter.mp hp).2] using hh
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_neg (by have := (mem_filter.mp hp).2; omega : ¬p ≤ v)] using hh
    · rintro ⟨hlo, hhi⟩ p hp
      apply (hcode p hp).mpr
      by_cases hpv : p ≤ v
      · simpa only [if_pos hpv] using hlo p (mem_filter.mpr ⟨hp, hpv⟩)
      · simpa only [if_neg hpv] using hhi p (mem_filter.mpr ⟨hp, by omega⟩)
  change |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} : ℝ) -
    (N : ℝ) * ∏ p ∈ S, nuN H p| ≤ cnt H (∏ p ∈ S, p)
  rw [hcount, hmain, hcnt]
  exact decompJ365_mixed_W_periodic_remainder N N d e le_rfl hd he hcop

/-- Clean supply of the finite mixed W leaf.
First memoir pages 88 and 89 and second memoir pages 106, 107 and 115.
The actual mixed residue count is kept separate from its density encoding. -/
theorem decomp338_mixed_w_finite_proved (a b N t v : ℕ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap N v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  let P := Nat.primesLE t
  let F := decomp338MixedWProduct N v t
  let H := decomp338EncodedGap N v t
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ P) :
      |(#{x ∈ range N | (∏ p ∈ S, p) ∣ F x} : ℝ) - (N : ℝ) * ∏ p ∈ S, nuN H p| ≤
        cnt H (∏ p ∈ S, p) := decomp338_mixed_W_remainder N v t S hS
  have hraw := decompJ365_decreasing_lower_explicit (range N) P J F hP cutoff level H N
    (nuN H) herror L hL hlevel
  apply hraw.trans
  have hincl : #{x ∈ range N | ∀ p ∈ P, ¬p ∣ F x} ≤
      #{x ∈ range N | (∀ p ∈ Nat.primesLE v, ¬p ∣ x * (N - x)) ∧
        ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ x} := by
    apply card_le_card
    intro x hx
    obtain ⟨hxN, hsurv⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hxN, ?_, ?_⟩
    · intro p hp hd
      obtain ⟨hpv, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpP : p ∈ P := Nat.mem_primesLE.mpr ⟨hpv.trans hvt, hpprime⟩
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_pos hpv] using hd
    · intro p hp hd
      obtain ⟨hpP, hpv⟩ := mem_sdiff.mp hp
      have hpv' : ¬p ≤ v := fun h => hpv (Nat.mem_primesLE.mpr ⟨h, hP p hpP⟩)
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_neg hpv'] using hd
  exact_mod_cast hincl.trans (decompJ365_mixed_survivors_le_wCount a b N t v hv hvt hthA hthB)

end
end LeanLab.Ricci1937
