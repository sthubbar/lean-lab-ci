import LeanLab.Ricci1937.Decomp338q

/-!
Ricci 1937, actual mixed Z residue encoding.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary actual mixed Z bad prime product.
Low primes divide x times x plus h. High primes divide the selected factor x plus k.
Taking k zero or h handles the two signs of the original shift.
First memoir page 75 and second memoir pages 106, 107 and 115. -/
def decomp338MixedZProduct (h k v t x : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primesLE t).filter (fun p =>
    if p ≤ v then p ∣ x * (x + h) else p ∣ x + k), p

/-- Auxiliary actual mixed Z residue discrepancy.
The selected high factor is translated by k and the density remains the encoded pair density.
First memoir pages 75 and 88 and second memoir pages 106, 107 and 115. -/
lemma decomp338_mixed_Z_remainder (h k N v t : ℕ) (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
    |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} : ℝ) -
      (N : ℝ) * ∏ p ∈ S, nuN (decomp338EncodedGap h v t) p| ≤
        cnt (decomp338EncodedGap h v t) (∏ p ∈ S, p) := by
  let H := decomp338EncodedGap h v t
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
  have hlow (p : ℕ) (hp : p ∈ A) : wt H p = wt h p := by
    have hh := decomp338_encoded_gap_low h v t p (hprimeA p hp) (mem_filter.mp hp).2
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeA p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeA p hp)] using hh
  have hhigh (p : ℕ) (hp : p ∈ B) : wt H p = 1 := by
    have hpt := (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
    have hh := decomp338_encoded_gap_high h v t p (hprimeB p hp) (mem_filter.mp hp).2 hpt
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeB p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeB p hp)] using hh
  have hcnt : (cnt H (∏ p ∈ S, p) : ℝ) = cnt h d := by
    rw [cnt_prod_primes H S hprime, cnt_prod_primes h A hprimeA]
    calc
      _ = (∏ p ∈ A, wt H p) * ∏ p ∈ B, wt H p := by rw [hAB, prod_union hdisj]
      _ = (∏ p ∈ A, wt h p) * 1 := by
        rw [prod_congr rfl hlow, prod_eq_one hhigh]
      _ = _ := mul_one _
  have hdensity : (cnt H (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) = ∏ p ∈ S, nuN H p := by
    rw [cnt_prod_primes H S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN H p) = (cnt h d : ℝ) * N / (d * e) := by
    rw [← hdensity, hcnt, hprod, Nat.cast_mul]
    ring
  have hcount : #{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} =
      #{x ∈ range N | d ∣ x * (x + h) ∧ e ∣ x + k} := by
    congr 1
    apply filter_congr
    intro x hx
    have hcode (p : ℕ) (hp : p ∈ S) : p ∣ decomp338MixedZProduct h k v t x ↔
        (if p ≤ v then p ∣ x * (x + h) else p ∣ x + k) :=
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
  change |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} : ℝ) -
    (N : ℝ) * ∏ p ∈ S, nuN H p| ≤ cnt H (∏ p ∈ S, p)
  rw [hcount, hmain, hcnt]
  exact decomp338_mixed_add_periodic_remainder h k N d e hd he hcop

end
end LeanLab.Ricci1937
