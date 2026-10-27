/-
AI wrote this Lean code for CODEX task03.
P0074, page 13, bounding the error after character orthogonality.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.CharacterL2

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Character error E controls every unit-residue test bounded by one with error sqrt φ times E. -/
theorem unit_test_bound {q : ℕ} [NeZero q] (A f : (ZMod q)ˣ → ℂ) (M : ℂ) {E : ℝ}
    (hE : 0 ≤ E)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ u : (ZMod q)ˣ, A u * χ (u : ZMod q)) - (if χ = 1 then M else 0)‖ ≤ E)
    (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖(∑ u : (ZMod q)ˣ, A u * f u) - M / q.totient * ∑ u : (ZMod q)ˣ, f u‖ ≤
      Real.sqrt q.totient * E := by
  classical
  let G : DirichletCharacter ℂ q → ℂ := fun χ => ∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)
  let D : DirichletCharacter ℂ q → ℂ := fun χ =>
    (∑ u : (ZMod q)ˣ, A u * χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q))) - if χ = 1 then M else 0
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hD : ∀ χ, ‖D χ‖ ≤ E := by
    intro χ
    have h := hχ χ⁻¹
    simpa only [D, MulChar.inv_apply, Ring.inverse_unit, inv_eq_one] using h
  have hmain : (∑ χ : DirichletCharacter ℂ q, G χ * (if χ = 1 then M else 0)) =
      M * ∑ u : (ZMod q)ˣ, f u := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, G,
      MulChar.one_apply_coe, mul_one]
    ring
  have hraw : (∑ χ : DirichletCharacter ℂ q, G χ *
      ∑ v : (ZMod q)ˣ, A v * χ (((v⁻¹ : (ZMod q)ˣ) : ZMod q))) =
      (q.totient : ℂ) * ∑ u : (ZMod q)ˣ, A u * f u := by
    calc
      _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, (f u * A v) *
          ∑ χ : DirichletCharacter ℂ q,
            χ (((v⁻¹ : (ZMod q)ˣ) : ZMod q)) * χ (u : ZMod q) := by
        simp only [G, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ hmem
        ring
      _ = _ := by
        simp_rw [← ZMod.inv_coe_unit,
          DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _)]
        simp only [Units.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        ring
  have heq : (q.totient : ℂ) *
      ((∑ u : (ZMod q)ˣ, A u * f u) - M / q.totient * ∑ u : (ZMod q)ˣ, f u) =
      ∑ χ : DirichletCharacter ℂ q, G χ * D χ := by
    dsimp only [D]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hraw, hmain]
    field_simp
  have hnorm : ‖∑ χ : DirichletCharacter ℂ q, G χ * D χ‖ ≤
      (q.totient : ℝ) * Real.sqrt q.totient * E := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖G χ * D χ‖ := norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖G χ‖ * E := by
        apply Finset.sum_le_sum
        intro χ hmem
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hD χ) (norm_nonneg _)
      _ = (∑ χ : DirichletCharacter ℂ q, ‖G χ‖) * E := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (character_coeff_l1 f hf) hE
  rw [← heq, norm_mul] at hnorm
  have hφnorm : ‖(q.totient : ℂ)‖ = (q.totient : ℝ) := by simp
  rw [hφnorm] at hnorm
  exact (mul_le_mul_iff_right₀ hφ).mp (by simpa only [mul_assoc] using hnorm)

#print axioms unit_test_bound
end LeanLab.Grimmelt2019.MainTerm
