/-
P0076 Lemma 5.4, page 19, in the prime modulus case.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.PrimeSieveFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Integer coprimality to a prime is nonvanishing in its residue field. -/
theorem int_isCoprime_prime_iff {p : ℕ} [Fact p.Prime] (x : ℤ) :
    IsCoprime x (p : ℤ) ↔ (x : ZMod p) ≠ 0 := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  change x.natAbs.Coprime p ↔ (x : ZMod p) ≠ 0
  rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd,
    ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]

/-- The positive sign character matches the paper exponential on natural representatives. -/
theorem stdAddChar_int_nat {p : ℕ} [NeZero p] (a : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((a : ZMod p) * (n : ZMod p)) = eC ((a : ℝ) * n / p) := by
  have h := ZMod.stdAddChar_coe (N := p) (a * n)
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I * ((a * n : ℤ) : ℂ) / p) := by
      convert h using 1 <;> push_cast <;> rfl
    _ = _ := by unfold eC; congr 1; push_cast; ring

/-- The prime modulus instance of the sum in display 5.5. -/
noncomputable def primeSieveSum (p : ℕ) (W V b a : ℤ) : ℂ :=
  ∑ n ∈ (range p).filter (fun n : ℕ => IsCoprime (W * V * n + b) (p : ℤ) ∧
    (p % 4 = 3 ∧ p ≠ 3 → IsCoprime (W * V * n + b - 1) (p : ℤ))),
    eC ((a : ℝ) * n / p)

/-- Transport the exact integer residue sum to the prime field. -/
theorem primeSieveSum_eq {p : ℕ} [Fact p.Prime] (W V b a : ℤ) :
    primeSieveSum p W V b a =
      ∑ x ∈ (univ : Finset (ZMod p)).filter (fun x =>
        (W : ZMod p) * V * x + b ≠ 0 ∧
        (p % 4 = 3 ∧ p ≠ 3 → (W : ZMod p) * V * x + b ≠ 1)),
        ZMod.stdAddChar ((a : ZMod p) * x) := by
  unfold primeSieveSum
  rw [sum_filter, ← sum_zmod_val (fun n => if IsCoprime (W * V * n + b) (p : ℤ) ∧
      (p % 4 = 3 ∧ p ≠ 3 → IsCoprime (W * V * n + b - 1) (p : ℤ)) then
      eC ((a : ℝ) * n / p) else 0), sum_filter]
  apply sum_congr rfl
  intro x _
  simp only [int_isCoprime_prime_iff, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_one, ZMod.natCast_zmod_val, sub_ne_zero]
  rw [← stdAddChar_int_nat, ZMod.natCast_zmod_val]

/-- The prime modulus sum is bounded by the two forbidden residues, uniformly in b. -/
theorem primeSieveSum_norm_le_two {p : ℕ} [Fact p.Prime] (W V b a : ℤ)
    (ha : IsCoprime a (p : ℤ)) : ‖primeSieveSum p W V b a‖ ≤ 2 := by
  have hak : (a : ZMod p) ≠ 0 := (int_isCoprime_prime_iff a).mp ha
  rw [primeSieveSum_eq]
  by_cases hp : p % 4 = 3 ∧ p ≠ 3
  · simpa [hp.1, hp.2] using affine_two_residue_bound ((W : ZMod p) * (V : ZMod p)) (b : ZMod p) (a : ZMod p) hak
  · have he : (univ : Finset (ZMod p)).filter (fun x =>
        (W : ZMod p) * V * x + b ≠ 0 ∧
        (p % 4 = 3 ∧ p ≠ 3 → (W : ZMod p) * V * x + b ≠ 1)) =
        univ.filter (fun x => (W : ZMod p) * V * x + b ≠ 0) := by
      ext x
      simp [hp]
    rw [he]
    exact (affine_one_residue_bound ((W : ZMod p) * (V : ZMod p)) (b : ZMod p) (a : ZMod p) hak).trans (by norm_num)

/-- When the prime divides W the character sum vanishes. -/
theorem primeSieveSum_eq_zero_of_dvd {p : ℕ} [Fact p.Prime] (W V b a : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hW : (p : ℤ) ∣ W) : primeSieveSum p W V b a = 0 := by
  have hW0 : (W : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd W p).mpr hW
  have hak : (a : ZMod p) ≠ 0 := (int_isCoprime_prime_iff a).mp ha
  rw [primeSieveSum_eq, hW0]
  simp only [zero_mul, zero_add, filter_const]
  split_ifs
  · simpa [mul_comm, hak] using LeanLab.Routes.R0001.sum_stdAddChar_mul (a : ZMod p)
  · simp

/-- Lemma 5.4 for prime q, with the printed coprimality indicator. -/
theorem lemma54_prime {p : ℕ} [Fact p.Prime] (W V b a : ℤ) (ha : IsCoprime a (p : ℤ)) :
    ‖primeSieveSum p W V b a‖ ≤ if IsCoprime (p : ℤ) W then 2 else 0 := by
  by_cases hcop : IsCoprime (p : ℤ) W
  · rw [if_pos hcop]
    exact primeSieveSum_norm_le_two W V b a ha
  · rw [if_neg hcop]
    have hW : (p : ℤ) ∣ W := by
      have h0 : ¬ (W : ZMod p) ≠ 0 := by
        intro hne
        exact hcop ((int_isCoprime_prime_iff W).mpr hne).symm
      have he : (W : ZMod p) = 0 := by simpa using h0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd W p).mp he
    rw [primeSieveSum_eq_zero_of_dvd W V b a ha hW, norm_zero]

/-- The prime case with the divisor count notation of display 5.5. -/
theorem lemma54_prime_divisor_count {p : ℕ} [Fact p.Prime] (W V b a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    ‖primeSieveSum p W V b a‖ ≤ (p.divisors.card : ℝ) *
      (if IsCoprime (p : ℤ) W then 1 else 0) := by
  have hpp : p.Prime := Fact.out
  have hcard : p.divisors.card = 2 := by simp [hpp.divisors, hpp.ne_one, Ne.symm hpp.ne_one]
  rw [hcard]
  have h := lemma54_prime W V b a ha
  split_ifs at h ⊢ <;> simpa using h

example : ‖primeSieveSum 5 1 1 0 1‖ ≤ 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact primeSieveSum_norm_le_two 1 1 0 1 (by norm_num)

#print axioms lemma54_prime_divisor_count

#print axioms int_isCoprime_prime_iff
#print axioms stdAddChar_int_nat
#print axioms primeSieveSum_eq
#print axioms primeSieveSum_norm_le_two
#print axioms primeSieveSum_eq_zero_of_dvd
#print axioms lemma54_prime

end LeanLab.Teravainen2016
