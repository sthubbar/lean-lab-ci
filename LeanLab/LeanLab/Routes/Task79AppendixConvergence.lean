/-
CODEX task79. AI wrote the Lean code. Binary Goldbach is open.
Convergence components of Chirre and Hagen Lemma A.1, printed page 13.
Source: https://arxiv.org/abs/2512.23534.
The numerical bounds remain CITED INPUTS from P0075 page 13, Lemma A.1, displays 1 to 3.
-/
import LeanLab.Routes.Task79AppendixA1

namespace LeanLab.Routes.Task79
open Real
open scoped BigOperators

theorem summable_log_sq_div_sq :
    Summable (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-3 / 2 : ℝ)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using hs.comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
    (Summable.mul_left (16 : ℝ) hshift)
  intro n
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  change Real.log a ^ 2 / a ^ 2 ≤ 16 * a ^ (-3 / 2 : ℝ)
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ha : 0 < a := by linarith
  have hl0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hl : Real.log a ≤ 4 * a ^ (1 / 4 : ℝ) := by
    nlinarith [Real.log_le_rpow_div ha.le (by norm_num : (0 : ℝ) < 1 / 4)]
  have hsq : Real.log a ^ 2 ≤ 16 * (a ^ (1 / 4 : ℝ)) ^ 2 := by
    have hm := mul_le_mul hl hl hl0 (by positivity : 0 ≤ 4 * a ^ (1 / 4 : ℝ))
    nlinarith
  have he : (a ^ (1 / 4 : ℝ)) ^ 2 / a ^ 2 = a ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (a ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul ha.le,
      ← Real.rpow_natCast a 2, ← Real.rpow_sub ha]
    norm_num
  calc
    _ ≤ (16 * (a ^ (1 / 4 : ℝ)) ^ 2) / a ^ 2 :=
      div_le_div_of_nonneg_right hsq (sq_nonneg a)
    _ = _ := by rw [mul_div_assoc, he]

theorem summable_log_div_three_halves :
    Summable (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-5 / 4 : ℝ)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using hs.comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
    (Summable.mul_left (4 : ℝ) hshift)
  intro n
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  change Real.log a / a ^ (3 / 2 : ℝ) ≤ 4 * a ^ (-5 / 4 : ℝ)
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ha : 0 < a := by linarith
  have hl : Real.log a ≤ 4 * a ^ (1 / 4 : ℝ) := by
    nlinarith [Real.log_le_rpow_div ha.le (by norm_num : (0 : ℝ) < 1 / 4)]
  calc
    _ ≤ (4 * a ^ (1 / 4 : ℝ)) / a ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_right hl (Real.rpow_nonneg ha.le _)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub ha]
      norm_num

theorem appendix_prime_sqrt_summable :
    Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) / (Real.sqrt ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))) := by
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q h
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    dsimp at h
    omega
  have hs : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
    apply (summable_log_div_three_halves.comp_injective hi).congr
    intro p
    change Real.log ((((p : ℕ) - 1 + 1 : ℕ) : ℝ)) /
      ((((p : ℕ) - 1 + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) = _
    rw [Nat.sub_add_cancel (by have := p.property.two_le; omega)]
  refine Summable.of_nonneg_of_le ?_ ?_ (Summable.mul_left (2 : ℝ) hs)
  · intro p
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
    exact div_nonneg (Real.log_nonneg (by linarith))
      (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
  · intro p
    let a : ℝ := ((p : ℕ) : ℝ)
    change Real.log a / (Real.sqrt a * (a - 1)) ≤ 2 * (Real.log a / a ^ (3 / 2 : ℝ))
    have ha2 : 2 ≤ a := by dsimp [a]; exact_mod_cast p.property.two_le
    have ha : 0 < a := by linarith
    have hl0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hden : Real.sqrt a * (a / 2) ≤ Real.sqrt a * (a - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg a)
    have he : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc
      _ ≤ Real.log a / (Real.sqrt a * (a / 2)) :=
        div_le_div_of_nonneg_left hl0 (by positivity) hden
      _ = _ := by
        rw [he]
        field_simp [ne_of_gt ha, ne_of_gt (Real.sqrt_pos.mpr ha)] <;> ring

theorem appendix_mangoldt_summable :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt (n + 1) ^ 2 /
      (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
    summable_log_sq_div_sq
  intro n
  have h0 : 0 ≤ ArithmeticFunction.vonMangoldt (n + 1) := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : ArithmeticFunction.vonMangoldt (n + 1) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _)

theorem appendix_prime_sq_summable :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ 2 /
      (((p : ℕ) : ℝ) ^ 2 - ((p : ℕ) : ℝ))) := by
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q h
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    dsimp at h
    omega
  have hs : Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ 2 / (((p : ℕ) : ℝ) ^ 2)) := by
    apply (summable_log_sq_div_sq.comp_injective hi).congr
    intro p
    change Real.log ((((p : ℕ) - 1 + 1 : ℕ) : ℝ)) ^ 2 /
      ((((p : ℕ) - 1 + 1 : ℕ) : ℝ) ^ 2) = _
    rw [Nat.sub_add_cancel (by have := p.property.two_le; omega)]
  refine Summable.of_nonneg_of_le ?_ ?_ (Summable.mul_left (2 : ℝ) hs)
  · intro p
    let a : ℝ := ((p : ℕ) : ℝ)
    change 0 ≤ Real.log a ^ 2 / (a ^ 2 - a)
    have ha2 : 2 ≤ a := by dsimp [a]; exact_mod_cast p.property.two_le
    exact div_nonneg (sq_nonneg _) (by nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ a - 1 by linarith)])
  · intro p
    let a : ℝ := ((p : ℕ) : ℝ)
    change Real.log a ^ 2 / (a ^ 2 - a) ≤ 2 * (Real.log a ^ 2 / a ^ 2)
    have ha2 : 2 ≤ a := by dsimp [a]; exact_mod_cast p.property.two_le
    have ha : 0 < a := by linarith
    have hden : a ^ 2 / 2 ≤ a ^ 2 - a := by
      nlinarith [mul_nonneg ha.le (show 0 ≤ a - 2 by linarith)]
    calc
      _ ≤ Real.log a ^ 2 / (a ^ 2 / 2) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ = _ := by field_simp <;> ring

theorem appendixA1_iff_bounds : AppendixA1 ↔
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) /
      (Real.sqrt ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))) < 1.7215 ∧
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2)) < 0.8053 ∧
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) ^ 2 /
      (((p : ℕ) : ℝ) ^ 2 - ((p : ℕ) : ℝ))) < 0.982 := by
  simp only [AppendixA1, appendix_prime_sqrt_summable, appendix_mangoldt_summable,
    appendix_prime_sq_summable, true_and]

end LeanLab.Routes.Task79
