import LeanLab.HardyLittlewood1923.GaussBound
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
AI wrote this Lean code for CODEX task52.
P0004 pages 8 and 9, expansion of additive phases by Dirichlet characters.
-/

open ZMod Finset

namespace LeanLab.HardyLittlewood1923.Task52

lemma additive_character_expansion {q : ℕ} [NeZero q]
    (e : AddChar (ZMod q) ℂ) {n : ZMod q} (hn : IsUnit n) :
    ∑ χ : DirichletCharacter ℂ q, χ n⁻¹ * gaussSum χ e = (q.totient : ℂ) * e n := by
  simp only [gaussSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ n⁻¹ * χ m) * e m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = _ := by
      simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hn]
      simp

lemma additive_character_expansion_div {q : ℕ} [NeZero q]
    (e : AddChar (ZMod q) ℂ) {n : ZMod q} (hn : IsUnit n) :
    e n = ∑ χ : DirichletCharacter ℂ q, (gaussSum χ e / (q.totient : ℂ)) * χ n⁻¹ := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have h := additive_character_expansion e hn
  apply (mul_right_cancel₀ hφ)
  rw [Finset.sum_mul]
  have ht (χ : DirichletCharacter ℂ q) :
      (gaussSum χ e / (q.totient : ℂ)) * χ n⁻¹ * (q.totient : ℂ) =
        χ n⁻¹ * gaussSum χ e := by
    field_simp
  simp_rw [ht]
  simpa only [mul_comm] using h.symm

lemma shifted_gauss_coefficient_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    ‖gaussSum χ (stdAddChar.mulShift (a : ZMod q)) / (q.totient : ℂ)‖ ≤
      Real.sqrt (q : ℝ) / (q.totient : ℝ) := by
  rw [gaussSum_mulShift_eq, norm_div, norm_mul,
    DirichletCharacter.unit_norm_eq_one, one_mul, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (gauss_norm_le χ) (Nat.cast_nonneg _)

#print axioms additive_character_expansion
#print axioms additive_character_expansion_div
#print axioms shifted_gauss_coefficient_bound

end LeanLab.HardyLittlewood1923.Task52
