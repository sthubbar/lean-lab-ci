import Mathlib.Analysis.Fourier.ZMod

/-!
AI wrote this Lean code for CODEX task52.
P0004 page 9 primitive Gauss sums, with the correction on page 69 respected.
-/

open ZMod

namespace LeanLab.HardyLittlewood1923.Task52

lemma primitive_gauss_product {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = (q : ℂ) * χ (-1) := by
  have hi : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv] using hχ
  have hf : 𝓕 (χ : ZMod q → ℂ) =
      gaussSum χ stdAddChar • (fun k => χ⁻¹ (-k)) := by
    funext k
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [hf, ZMod.dft_const_smul, ZMod.dft_comp_neg] at h
  simpa only [Pi.smul_apply, smul_eq_mul, hi.fourierTransform_eq_inv_mul_gaussSum,
    inv_inv, neg_neg, map_one, one_mul] using h

lemma primitive_gauss_norm_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = (q : ℝ) := by
  have hi : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv] using hχ
  have he : (stdAddChar : AddChar (ZMod q) ℂ)⁻¹ = stdAddChar.mulShift (-1) := by
    ext x
    simp [AddChar.mulShift_apply]
  have hs : star (gaussSum χ stdAddChar) = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq, he, gaussSum_mulShift_of_isPrimitive _ hi, inv_inv]
  have hm : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  have hp : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = (q : ℂ) := by
    rw [hs, mul_left_comm, primitive_gauss_product hχ]
    calc _ = (q : ℂ) * (χ (-1) * χ (-1)) := by ring
      _ = _ := by rw [hm, mul_one]
  have hn := Complex.mul_conj (gaussSum χ stdAddChar)
  rw [← Complex.star_def, hp, Complex.normSq_eq_norm_sq] at hn
  exact_mod_cast hn.symm

lemma primitive_gauss_norm {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ = Real.sqrt (q : ℝ) := by
  rw [← primitive_gauss_norm_sq hχ, Real.sqrt_sq (norm_nonneg _)]

#print axioms primitive_gauss_product
#print axioms primitive_gauss_norm_sq
#print axioms primitive_gauss_norm

end LeanLab.HardyLittlewood1923.Task52
