import LeanLab.Ricci1937.Decomp338r

/-!
Ricci 1937, mixed Z survivor inclusion.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary mixed Z survivor inclusion for both signs of the shift.
The first factor avoids primes through t and the translated factor avoids primes through v.
First memoir pages 75 and 88 and second memoir page 115. -/
lemma decomp338_mixed_survivors_le_zCount (a b ξ N t v : ℕ) (m : ℤ)
    (hv : 2 ≤ v) (hvt : v ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v) :
    #{y ∈ range N | (∀ p ∈ Nat.primesLE v, ¬ p ∣ y * (y + 2 * m.natAbs)) ∧
      ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ y + (if 0 ≤ m then 0 else 2 * m.natAbs)} ≤
      zCount a b m ξ := by
  have ht : 2 ≤ t := hv.trans hvt
  let h := 2 * m.natAbs
  let f : ℕ → ℕ := fun y => if 0 ≤ m then y else y + h
  have hgap : (h : ℤ) = 2 * |m| := by simp [h, Int.natCast_natAbs]
  have hvalues (y : ℕ) :
      (f y : ℤ) + 2 * m = if 0 ≤ m then (y + h : ℕ) else y := by
    dsimp [f]
    split_ifs with hm
    · rw [abs_of_nonneg hm] at hgap
      push_cast
      omega
    · rw [abs_of_neg (lt_of_not_ge hm)] at hgap
      push_cast
      omega
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    obtain ⟨hyN, hlo, hhi⟩ := mem_filter.mp hy
    have hylt := mem_range.mp hyN
    have hy0 : 0 < y := by
      by_contra hy
      have hz : y = 0 := by omega
      have htwo : 2 ∈ Nat.primesLE v := Nat.mem_primesLE.mpr ⟨hv, Nat.prime_two⟩
      exact hlo 2 htwo (by simp [hz])
    have hyξ : y + h ≤ ξ := by dsimp [h]; omega
    have hx1 : 1 ≤ f y := by dsimp [f]; split_ifs <;> omega
    have hxξ : f y ≤ ξ := by dsimp [f]; split_ifs <;> omega
    have hbpos : 0 < (f y : ℤ) + 2 * m := by
      rw [hvalues]
      split_ifs <;> positivity
    have hrough (z : ℕ) (hz : z = y ∨ z = y + h) :
        ∀ p ∈ z.primeFactorsList, (v : ℝ) < p := by
      intro p hp
      have hz0 : z ≠ 0 := by rcases hz with rfl | rfl <;> omega
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hz0).mp hp
      by_contra htp
      have hpt : p ≤ v := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ v)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      apply hlo p hpP
      rcases hz with rfl | rfl
      · exact dvd_mul_of_dvd_left hpdvd _
      · exact dvd_mul_of_dvd_right hpdvd _
    have hfy : f y = y ∨ f y = y + h := by dsimp [f]; split_ifs <;> simp
    have hroughA : ∀ p ∈ (f y).primeFactorsList, (t : ℝ) < p := by
      intro p hp
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : f y ≠ 0)).mp hp
      by_contra htp
      have hpt : p ≤ t := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ t)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      by_cases hpv : p ≤ v
      · apply hlo p (Nat.mem_primesLE.mpr ⟨hpv, hpprime⟩)
        rcases hfy with hf | hf
        · rw [hf] at hpdvd
          exact dvd_mul_of_dvd_left hpdvd _
        · rw [hf] at hpdvd
          exact dvd_mul_of_dvd_right hpdvd _
      · apply hhi p (mem_sdiff.mpr ⟨hpP, fun hp => hpv (Nat.mem_primesLE.mp hp).1⟩)
        dsimp [f, h] at hpdvd
        split_ifs at hpdvd ⊢ <;> simpa using hpdvd
    have hbval : ((f y : ℤ) + 2 * m).toNat = if 0 ≤ m then y + h else y := by
      rw [hvalues]
      split_ifs <;> norm_cast
    have hb1 : 1 ≤ ((f y : ℤ) + 2 * m).toNat := by rw [hbval]; split_ifs <;> omega
    have hbξ : ((f y : ℤ) + 2 * m).toNat ≤ ξ := by rw [hbval]; split_ifs <;> omega
    have hbchoices : ((f y : ℤ) + 2 * m).toNat = y ∨
        ((f y : ℤ) + 2 * m).toNat = y + h := by rw [hbval]; split_ifs <;> simp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast (by omega : 1 ≤ v)
    have hA := almostGT_of_pow_bound hx1 ht1 hroughA
      ((by exact_mod_cast hxξ : (f y : ℝ) ≤ ξ).trans_lt hsizeA)
    have hB := almostGT_of_pow_bound hb1 hv1 (hrough _ hbchoices)
      ((by exact_mod_cast hbξ : (((f y : ℤ) + 2 * m).toNat : ℝ) ≤ ξ).trans_lt hsizeB)
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hx1, hxξ⟩, almostGT_mono hA le_rfl ?_, hbpos,
      almostGT_mono hB le_rfl ?_⟩
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthA
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthB
  · intro y _ z _ heq
    dsimp [f] at heq
    split_ifs at heq <;> omega


end
end LeanLab.Ricci1937
