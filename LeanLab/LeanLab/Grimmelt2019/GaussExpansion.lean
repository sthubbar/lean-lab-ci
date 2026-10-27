/-
AI wrote this Lean code for CODEX task51.
P0074 page 9, equation 27 and the following character expansion.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.GaussBounds
import LeanLab.Grimmelt2019.Characters

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- Character orthogonality recovers the additive character at each unit. -/
theorem gauss_expansion_unit {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ZMod.stdAddChar (u : ZMod q) = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (u : ZMod q) := by
  have hinv : (∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ ZMod.stdAddChar * χ (u : ZMod q)) =
      ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ ZMod.stdAddChar * χ⁻¹ (u : ZMod q) := by
    simpa only [Equiv.inv_apply, inv_inv] using
      Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q))
        (fun χ : DirichletCharacter ℂ q => gaussSum χ ZMod.stdAddChar * χ⁻¹ (u : ZMod q))
  have hi : ∀ χ : DirichletCharacter ℂ q,
      χ⁻¹ (u : ZMod q) = χ ((u : ZMod q)⁻¹) := by
    intro χ
    rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hraw : (∑ χ : DirichletCharacter ℂ q,
      gaussSum χ ZMod.stdAddChar * χ⁻¹ (u : ZMod q)) =
      (q.totient : ℂ) * ZMod.stdAddChar (u : ZMod q) := by
    simp only [gaussSum, Finset.sum_mul, hi]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar x *
          ∑ χ : DirichletCharacter ℂ q, χ ((u : ZMod q)⁻¹) * χ x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ hχ
        ring
      _ = _ := by
        simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  rw [hinv, hraw]
  field_simp

/-- Equation 27 for every integer coprime to the modulus. -/
theorem gauss_expansion_coprime {q : ℕ} [NeZero q] (m : ℤ) (hm : Int.gcd m q = 1) :
    LeanLab.PNTPort.LargeSieve.e ((m : ℝ) / q) = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ ZMod.stdAddChar * χ (m : ZMod q) := by
  have hu : IsUnit (m : ZMod q) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]
    exact hm
  have he : ZMod.stdAddChar (m : ZMod q) = LeanLab.PNTPort.LargeSieve.e ((m : ℝ) / q) := by
    simpa only [Nat.cast_one, mul_one, Int.cast_one, one_div, ← div_eq_mul_inv] using
      stdAddChar_mul_natCast (q := q) m 1
  have h := gauss_expansion_unit hu.unit
  simpa only [hu.unit_spec, he] using h

/-- Rough support converts a finite exponential sum to the paper's character expansion. -/
theorem gauss_weighted_expansion {q : ℕ} [NeZero q] (W : Finset ℤ) (ν : ℤ → ℝ)
    (r : ℤ) (hr : Int.gcd r q = 1)
    (hs : ∀ n ∈ W, ν n ≠ 0 → Int.gcd n q = 1) :
    (∑ n ∈ W, (ν n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          ∑ n ∈ W, (ν n : ℂ) * χ (n : ZMod q) := by
  have hterm : ∀ n ∈ W,
      (ν n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) * ((ν n : ℂ) * χ (n : ZMod q)) := by
    intro n hn
    by_cases hz : ν n = 0
    · simp [hz]
    · have hr' : IsCoprime r (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hr
      have hn' : IsCoprime n (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (hs n hn hz)
      have hcop := Int.isCoprime_iff_gcd_eq_one.mp (hr'.mul_left hn')
      have he := gauss_expansion_coprime (q := q) (r * n) hcop
      rw [Int.cast_mul] at he
      rw [he]
      simp only [Int.cast_mul, map_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.mul_sum]

#print axioms gauss_expansion_unit
#print axioms gauss_expansion_coprime
#print axioms gauss_weighted_expansion
end LeanLab.Grimmelt2019.MainTerm
