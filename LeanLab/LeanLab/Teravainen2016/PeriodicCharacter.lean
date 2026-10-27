/-
P0076 Lemma 5.4, pages 19 to 20, orthogonality in display 5.8.
A translation preserving the sieve weight forces a primitive character sum to vanish.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.PrimeLemma54

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A weight invariant under a nontrivial character translation has zero character sum. -/
theorem weighted_character_sum_eq_zero {N : ℕ} [NeZero N]
    (a t : ZMod N) (w : ZMod N → ℂ)
    (hw : ∀ x, w (x + t) = w x) (ht : ZMod.stdAddChar (a * t) ≠ 1) :
    ∑ x : ZMod N, w x * ZMod.stdAddChar (a * x) = 0 := by
  have hs : (∑ x : ZMod N, w x * ZMod.stdAddChar (a * x)) *
      ZMod.stdAddChar (a * t) = ∑ x : ZMod N, w x * ZMod.stdAddChar (a * x) := by
    calc
      _ = ∑ x : ZMod N, w (x + t) * ZMod.stdAddChar (a * (x + t)) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        rw [hw, mul_add, AddChar.map_add_eq_mul]
        ring
      _ = _ := Equiv.sum_comp (Equiv.addRight t) (fun x => w x * ZMod.stdAddChar (a * x))
  have hz : (∑ x : ZMod N, w x * ZMod.stdAddChar (a * x)) *
      (ZMod.stdAddChar (a * t) - 1) = 0 := by linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr ht)

/-- For unit frequency every nonzero period kills the weighted sum. -/
theorem weighted_character_sum_eq_zero_of_unit {N : ℕ} [NeZero N]
    (a t : ZMod N) (ha : IsUnit a) (ht : t ≠ 0) (w : ZMod N → ℂ)
    (hw : ∀ x, w (x + t) = w x) :
    ∑ x : ZMod N, w x * ZMod.stdAddChar (a * x) = 0 := by
  apply weighted_character_sum_eq_zero a t w hw
  intro he
  have haz : a * t = 0 := ZMod.injective_stdAddChar (by simpa using he)
  exact ht ((ha.mul_right_injective).eq_iff.mp (by simpa using haz))

/-- A sifted set invariant under a nonzero translation has zero sum at unit frequency. -/
theorem sifted_character_sum_eq_zero_of_period {N : ℕ} [NeZero N]
    (a t : ZMod N) (ha : IsUnit a) (ht : t ≠ 0) (S : Finset (ZMod N))
    (hS : ∀ x, x + t ∈ S ↔ x ∈ S) :
    ∑ x ∈ S, ZMod.stdAddChar (a * x) = 0 := by
  have hw : ∀ x, (if x + t ∈ S then (1 : ℂ) else 0) =
      (if x ∈ S then (1 : ℂ) else 0) := by
    intro x
    simp only [hS]
  have h := weighted_character_sum_eq_zero_of_unit a t ha ht
    (fun x => if x ∈ S then 1 else 0) hw
  simpa only [ite_mul, one_mul, zero_mul, sum_ite_mem, univ_inter] using h

/-- A weight lifted from a proper divisor modulus has no primitive Fourier coefficient. -/
theorem lifted_weight_character_sum_eq_zero {N d : ℕ} [NeZero N]
    (hd0 : 0 < d) (hdN : d < N) (hd : d ∣ N)
    (a : ZMod N) (ha : IsUnit a) (w : ZMod d → ℂ) :
    ∑ x : ZMod N, w (ZMod.castHom hd (ZMod d) x) * ZMod.stdAddChar (a * x) = 0 := by
  have hperiod : (d : ZMod N) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd0 hdN
  apply weighted_character_sum_eq_zero_of_unit a d ha hperiod
  intro x
  simp only [map_add, map_natCast, ZMod.natCast_self, add_zero]

/-- Every weight depending only on a prime residue has zero primitive sum modulo a higher power. -/
theorem prime_power_lifted_weight_sum_eq_zero {p k : ℕ} [NeZero p] (hp : p.Prime) (hk : 2 ≤ k)
    (a : ℕ) (ha : a.Coprime (p ^ k)) (w : ZMod p → ℂ) :
    let hd : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
    ∑ x : ZMod (p ^ k), w (ZMod.castHom hd (ZMod p) x) *
      ZMod.stdAddChar ((a : ZMod (p ^ k)) * x) = 0 := by
  dsimp only
  apply lifted_weight_character_sum_eq_zero hp.pos _ _ (a : ZMod (p ^ k))
    ((ZMod.isUnit_iff_coprime a (p ^ k)).mpr ha) w
  calc
    p = p ^ 1 := (pow_one p).symm
    _ < p ^ k := (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by omega)

example : ∑ x : ZMod 4, (1 : ℂ) * ZMod.stdAddChar ((1 : ZMod 4) * x) = 0 := by
  apply weighted_character_sum_eq_zero_of_unit 1 2 isUnit_one (by decide)
  intro x
  rfl

#print axioms lifted_weight_character_sum_eq_zero
#print axioms prime_power_lifted_weight_sum_eq_zero
#print axioms weighted_character_sum_eq_zero
#print axioms weighted_character_sum_eq_zero_of_unit
#print axioms sifted_character_sum_eq_zero_of_period

end LeanLab.Teravainen2016
