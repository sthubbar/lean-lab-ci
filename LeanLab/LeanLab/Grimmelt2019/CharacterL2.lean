/-
AI wrote this Lean code for CODEX task03.
P0074, page 13, the averaged character coefficient bound in the main term error.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Characters
import LeanLab.Grimmelt2019.Ramanujan
import Mathlib.NumberTheory.MulChar.Lemmas

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Conjugation of a character value on a unit is evaluation at the inverse unit. -/
theorem character_conj_unit {q : ℕ} (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    (starRingEnd ℂ) (χ (u : ZMod q)) = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

/-- Parseval for the character coefficients of a function on the unit residues. -/
theorem character_parseval {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖ ^ 2 =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  calc
    ((∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖ ^ 2 : ℝ) : ℂ)
        = ∑ χ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (f u * χ (u : ZMod q)) * (starRingEnd ℂ) (f v * χ (v : ZMod q)) := by
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro χ hχ
            exact LeanLab.PNTPort.LargeSieve.ofReal_normSq_sum _ _
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (f u * (starRingEnd ℂ) (f v)) *
            ∑ χ : DirichletCharacter ℂ q,
              χ (((v⁻¹ : (ZMod q)ˣ) : ZMod q)) * χ (u : ZMod q) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [map_mul, character_conj_unit]
      ring
    _ = (q.totient : ℂ) * ∑ u : (ZMod q)ˣ, f u * (starRingEnd ℂ) (f u) := by
      simp_rw [← ZMod.inv_coe_unit,
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _)]
      simp only [Units.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = (((q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [Complex.ofReal_pow] using Complex.mul_conj' (f u)

/-- A function bounded by one has total character coefficient norm at most φ times sqrt φ. -/
theorem character_coeff_l1 {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ)
    (hf : ∀ u, ‖f u‖ ≤ 1) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖ ≤
      (q.totient : ℝ) * Real.sqrt q.totient := by
  classical
  have hφ : (0 : ℝ) ≤ q.totient := by positivity
  have hcardχ : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hcardu : (Fintype.card (ZMod q)ˣ : ℝ) = q.totient := by
    rw [ZMod.card_units_eq_totient]
  have hsum : ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 ≤ (q.totient : ℝ) := by
    calc
      _ ≤ ∑ _u : (ZMod q)ˣ, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact pow_le_one₀ (norm_nonneg _) (hf u)
      _ = (q.totient : ℝ) := by simp [hcardu]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun χ : DirichletCharacter ℂ q => ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖)
    (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  rw [character_parseval, hcardχ] at hcs
  have hsquare : (∑ χ : DirichletCharacter ℂ q,
      ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖) ^ 2 ≤ (q.totient : ℝ) ^ 3 := by
    apply hcs.trans
    calc (q.totient : ℝ) * (∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2) * q.totient
        ≤ (q.totient : ℝ) * q.totient * q.totient := by gcongr
      _ = _ := by ring
  have hright : ((q.totient : ℝ) * Real.sqrt q.totient) ^ 2 = (q.totient : ℝ) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hφ]
    ring
  have hnonneg : 0 ≤ (q.totient : ℝ) * Real.sqrt q.totient := by positivity
  nlinarith [Finset.sum_nonneg (fun (χ : DirichletCharacter ℂ q) (_ : χ ∈ Finset.univ) =>
    norm_nonneg (∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)))]

#print axioms character_coeff_l1
#print axioms character_conj_unit
#print axioms character_parseval
end LeanLab.Grimmelt2019.MainTerm
