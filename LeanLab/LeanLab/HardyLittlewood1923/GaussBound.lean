import LeanLab.HardyLittlewood1923.PrimitiveGauss
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib

/-!
AI wrote this Lean code for CODEX task52.
The bound on page 9 of P0004 is used with its correction on pages 69 and 70.
-/

open ZMod Finset

namespace LeanLab.HardyLittlewood1923.Task52

lemma dft_bilinear {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    ∑ k, ZMod.dft f k * g k = ∑ j, f j * ZMod.dft g j := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm k j]
  ring

lemma dft_star {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (fun j => star (f j)) k = star (ZMod.dft f (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp [← starRingEnd_apply, ← AddChar.map_neg_eq_conj, mul_comm]

lemma dft_parseval {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ k, ‖ZMod.dft f k‖ ^ 2 = (q : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have h := dft_bilinear f (fun k => star (ZMod.dft f k))
  have he (j : ZMod q) : ZMod.dft (fun k => star (ZMod.dft f k)) j =
      (q : ℂ) * star (f j) := by
    rw [dft_star, ZMod.dft_dft]
    simp
  simp_rw [he] at h
  have hm (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj z
  simp_rw [mul_left_comm (f _) (q : ℂ), hm] at h
  rw [← Finset.mul_sum] at h
  exact_mod_cast h

lemma gauss_norm_sq_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ stdAddChar‖ ^ 2 ≤ (q : ℝ) := by
  have hp (k : ZMod q) :
      ‖χ k‖ ^ 2 * ‖gaussSum χ stdAddChar‖ ^ 2 ≤ ‖ZMod.dft χ k‖ ^ 2 := by
    by_cases hk : IsUnit k
    · obtain ⟨u, rfl⟩ := hk
      rw [DirichletCharacter.unit_norm_eq_one, one_pow, one_mul,
        DirichletCharacter.fourierTransform_eq_gaussSum_mulShift]
      have he : stdAddChar.mulShift (-(u : ZMod q)) =
          (stdAddChar : AddChar (ZMod q) ℂ).mulShift ((-u : (ZMod q)ˣ) : ZMod q) := rfl
      rw [he, gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
    · rw [χ.map_nonunit hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      positivity
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod q))) (fun k _ => hp k)
  rw [← Finset.sum_mul, dft_parseval] at hs
  have hpos : 0 < ∑ k : ZMod q, ‖χ k‖ ^ 2 := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ (univ : Finset (ZMod q))) =>
      sq_nonneg ‖χ k‖) (Finset.mem_univ (1 : ZMod q))
    simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by simpa using h)
  nlinarith only [hs, hpos]

lemma gauss_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ stdAddChar‖ ≤ Real.sqrt (q : ℝ) := by
  have h := gauss_norm_sq_le χ
  have hs := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith [norm_nonneg (gaussSum χ stdAddChar), Real.sqrt_nonneg (q : ℝ)]

#print axioms dft_bilinear
#print axioms dft_star
#print axioms dft_parseval
#print axioms gauss_norm_sq_le
#print axioms gauss_norm_le

end LeanLab.HardyLittlewood1923.Task52
