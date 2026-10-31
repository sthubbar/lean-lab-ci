/-
P0076 Lemma 5.4, pages 19 to 20, higher prime power vanishing.
This is the exact residue sum in display 5.5 for q equal to a prime power.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.PeriodicCharacter

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The local sieve sum at modulus p to the power k, with natural frequency a. -/
noncomputable def primePowerSieveSum (p k : ℕ) (W V b : ℤ) (a : ℕ) : ℂ :=
  ∑ n ∈ (range (p ^ k)).filter (fun n : ℕ => IsCoprime (W * V * n + b) ((p : ℤ) ^ k) ∧
    (p % 4 = 3 ∧ p ≠ 3 → IsCoprime (W * V * n + b - 1) ((p : ℤ) ^ k))),
    eC ((a : ℝ) * n / (p ^ k : ℕ))

/-- Transport the exact integer sum to a weight lifted from residues modulo p. -/
theorem primePowerSieveSum_eq_lift {p k : ℕ} [Fact p.Prime] (hk : 0 < k)
    (W V b : ℤ) (a : ℕ) :
    primePowerSieveSum p k W V b a =
      ∑ x : ZMod (p ^ k),
        (if (W : ZMod p) * V * (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) + b ≠ 0 ∧
            (p % 4 = 3 ∧ p ≠ 3 →
              (W : ZMod p) * V * (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) + b ≠ 1)
          then (1 : ℂ) else 0) * ZMod.stdAddChar ((a : ZMod (p ^ k)) * x) := by
  unfold primePowerSieveSum
  rw [sum_filter, ← sum_zmod_val (fun n => if IsCoprime (W * V * n + b) ((p : ℤ) ^ k) ∧
      (p % 4 = 3 ∧ p ≠ 3 → IsCoprime (W * V * n + b - 1) ((p : ℤ) ^ k)) then
      eC ((a : ℝ) * n / (p ^ k : ℕ)) else 0)]
  apply sum_congr rfl
  intro x _
  simp only [IsCoprime.pow_right_iff hk, int_isCoprime_prime_iff, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, sub_ne_zero,
    ZMod.castHom_apply, ZMod.cast_eq_val]
  have hchar : ZMod.stdAddChar ((a : ZMod (p ^ k)) * x) =
      eC ((a : ℝ) * x.val / (p ^ k : ℕ)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (stdAddChar_int_nat (p := p ^ k) (a : ℤ) x.val)
  rw [hchar]
  split_ifs <;> simp

/-- The sieve sum vanishes at every higher prime power with coprime frequency. -/
theorem primePowerSieveSum_eq_zero {p k : ℕ} [Fact p.Prime] (hk : 2 ≤ k)
    (W V b : ℤ) (a : ℕ) (ha : a.Coprime (p ^ k)) :
    primePowerSieveSum p k W V b a = 0 := by
  have hk0 : 0 < k := by omega
  rw [primePowerSieveSum_eq_lift hk0]
  exact prime_power_lifted_weight_sum_eq_zero (Fact.out : p.Prime) hk a ha
    (fun y : ZMod p => if (W : ZMod p) * V * y + b ≠ 0 ∧
      (p % 4 = 3 ∧ p ≠ 3 → (W : ZMod p) * V * y + b ≠ 1) then 1 else 0)

/-- The prime exponent one recovers the existing prime modulus sum. -/
theorem primePowerSieveSum_one (p : ℕ) (W V b : ℤ) (a : ℕ) :
    primePowerSieveSum p 1 W V b a = primeSieveSum p W V b a := by
  simp only [primePowerSieveSum, pow_one, primeSieveSum, Int.cast_natCast]

example : primePowerSieveSum 7 2 1 1 0 1 = 0 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact primePowerSieveSum_eq_zero (by decide) 1 1 0 1 (by decide)

#print axioms primePowerSieveSum_eq_lift
#print axioms primePowerSieveSum_eq_zero
#print axioms primePowerSieveSum_one

end LeanLab.Teravainen2016
