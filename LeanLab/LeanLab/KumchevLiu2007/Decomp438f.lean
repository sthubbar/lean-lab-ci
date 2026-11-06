/-
Vanishing of reduced quadratic sums at higher prime powers.
Source page 13 property ii and Schwarz Part II page 82 Lemma 2.1.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438e

namespace LeanLab.KumchevLiu2007.Task438f

open Real Complex U1534 Task129c
open scoped BigOperators

/-- Schwarz page 82 Lemma 2.1, elementary translation proof.
A square zero residue h with 2h nonzero forces every unit frequency
reduced quadratic character sum to vanish. -/
theorem quadratic_sum_zero_of_square_zero (q : ℕ) [NeZero q]
    (a h : ZMod q) (ha : IsUnit a) (hh : h ^ 2 = 0) (h2 : 2 * h ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)) = 0 := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter IsUnit
  let f : ZMod q → ℂ := fun x => ZMod.stdAddChar (N := q) (a * x * x)
  have hnil (t : ZMod q) : IsNilpotent (t * h) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, hh, mul_zero]
  have hshift (t : ZMod q) : (∑ x ∈ U, f (x + t * h)) = ∑ x ∈ U, f x := by
    refine Finset.sum_bij (fun x _ => x + t * h) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil t).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx y hy hxy
      exact add_right_cancel hxy
    · intro x hx
      refine ⟨x + (-t) * h, ?_, by ring⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil (-t)).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx
      rfl
  have hinner (x : ZMod q) (hx : x ∈ U) : (∑ t : ZMod q, f (x + t * h)) = 0 := by
    have hxU : IsUnit x := (Finset.mem_filter.mp hx).2
    have hc : 2 * a * x * h ≠ 0 := by
      have he : 2 * a * x * h = (a * x) * (2 * h) := by ring
      rw [he]
      exact fun hz => h2 ((ha.mul hxU).mul_right_eq_zero.mp hz)
    have he (t : ZMod q) : f (x + t * h) =
        f x * ZMod.stdAddChar (N := q) (t * (2 * a * x * h)) := by
      have halg : a * (x + t * h) * (x + t * h) = a * x * x + t * (2 * a * x * h) := by
        have hsq : h * h = 0 := by simpa [sq] using hh
        linear_combination a * t ^ 2 * hsq
      dsimp [f]
      rw [halg, AddChar.map_add_eq_mul]
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q))
      (2 * a * x * h) (ZMod.isPrimitive_stdAddChar q)
    simp only [ite_eq_right hc, Nat.cast_zero] at hs
    rw [hs, mul_zero]
  have he : (q : ℂ) * (∑ x ∈ U, f x) = 0 := by
    calc
      _ = ∑ t : ZMod q, ∑ x ∈ U, f (x + t * h) := by simp [hshift]
      _ = ∑ x ∈ U, ∑ t : ZMod q, f (x + t * h) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero hinner
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  exact (mul_eq_zero.mp he).resolve_left hq0

/-- Schwarz page 82 Lemma 2.1. An admissible exponent d gives a square zero
translation modulo p to k and a nonzero doubled translation. -/
theorem quadratic_sum_prime_power_zero (p k d : ℕ) [NeZero (p ^ k)] (hp : 0 < p)
    (hkd : k ≤ 2 * d) (hsmall : 0 < 2 * p ^ d) (hlarge : 2 * p ^ d < p ^ k)
    (a : ZMod (p ^ k)) (ha : IsUnit a) :
    (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ k))).filter IsUnit,
      ZMod.stdAddChar (N := p ^ k) (a * x * x)) = 0 := by
  classical
  apply quadratic_sum_zero_of_square_zero (p ^ k) a ((p ^ d : ℕ) : ZMod (p ^ k)) ha
  · have hd : p ^ k ∣ (p ^ d) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hd
  · have hd : ¬ p ^ k ∣ 2 * p ^ d := Nat.not_dvd_of_pos_of_lt hsmall hlarge
    rw [show (2 : ZMod (p ^ k)) * ((p ^ d : ℕ) : ZMod (p ^ k)) =
      ((2 * p ^ d : ℕ) : ZMod (p ^ k)) by push_cast; rfl]
    exact fun hz => hd ((ZMod.natCast_eq_zero_iff _ _).mp hz)

/-- Page 13 property ii and Schwarz page 82 Lemma 2.1.
Every reduced quadratic sum at a unit frequency vanishes at an odd prime
power from exponent 2 and at a power of 2 from exponent 4. -/
theorem gaussS_prime_power_vanish (p k a : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) (ha : a.Coprime (p ^ k)) :
    gaussS (p ^ k) a = 0 := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hau : IsUnit (a : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime a (p ^ k)).mpr ha
  rw [Task342h.gaussS_zmod]
  rcases hk with ⟨hodd, hk⟩ | ⟨rfl, hk⟩
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
    have hpk : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    apply quadratic_sum_prime_power_zero p k (k - 1) hp.pos (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right hp2 (by positivity)) _ hau
  · have hpk : 2 ^ k = 4 * 2 ^ (k - 2) := by
      conv_lhs => rw [show k = 2 + (k - 2) by omega, pow_add]
      norm_num
    apply quadratic_sum_prime_power_zero 2 k (k - 2) (by norm_num) (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) _ hau

/-- Page 13 property ii. Exact prime power coefficient vanishing supply.
The vanishing reduced quadratic sum kills every term of the coefficient. -/
theorem A3_prime_power_vanish (n p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    A3 n (p ^ k) = 0 := by
  unfold A3
  have hs : (∑ a ∈ (Finset.range (p ^ k)).filter (fun a => Nat.Coprime a (p ^ k)),
      gaussS (p ^ k) a ^ 3 * ee (-((a * n : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [gaussS_prime_power_vanish p k a hp hk (Finset.mem_filter.mp ha).2]
    simp
  rw [hs, mul_zero]

#print axioms quadratic_sum_zero_of_square_zero
#print axioms quadratic_sum_prime_power_zero
#print axioms gaussS_prime_power_vanish
#print axioms A3_prime_power_vanish

end LeanLab.KumchevLiu2007.Task438f
