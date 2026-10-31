/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 4.3, page 20. Primitive character twists.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101FourierSieve
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open Finset ComplexConjugate

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Complex conjugation reverses the sign of the discrete Fourier frequency. -/
theorem dft_conj {r : ℕ} [NeZero r] (f : ZMod r → ℂ) (k : ZMod r) :
    ZMod.dft (fun n => conj (f n)) k = conj (ZMod.dft f (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, mul_neg, neg_neg]
  apply sum_congr rfl
  intro n _
  rw [AddChar.map_neg_eq_inv]
  have hn : ‖ZMod.stdAddChar (n * k)‖ = 1 := by
    change ‖(ZMod.toCircle (n * k) : ℂ)‖ = 1
    simp
  rw [Complex.inv_eq_conj hn]

/-- The standard Gauss sum of a primitive character has squared norm r. -/
theorem primitive_gauss_norm_sq {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = r := by
  let τ : ℂ := gaussSum χ ZMod.stdAddChar
  have hF : ZMod.dft (χ : ZMod r → ℂ) =
      fun k => τ * χ⁻¹ (-k) := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    exact mul_comm _ _
  have hFF := congrFun (ZMod.dft_dft (χ : ZMod r → ℂ)) (-1)
  rw [hF, ZMod.dft_const_mul, ZMod.dft_comp_neg] at hFF
  have hc : ((χ⁻¹ : DirichletCharacter ℂ r) : ZMod r → ℂ) = fun n => conj (χ n) := by
    funext n
    exact (MulChar.star_apply' χ n).symm
  rw [hc] at hFF
  have hx : τ * ZMod.dft (fun n : ZMod r => conj (χ n)) 1 = (r : ℂ) * χ 1 := by
    simpa only [neg_neg, smul_eq_mul] using hFF
  rw [dft_conj] at hx
  simp only [neg_neg, hχ.fourierTransform_eq_inv_mul_gaussSum,
    map_one, one_mul, mul_one] at hx
  rw [Complex.mul_conj'] at hx
  exact_mod_cast hx

/-- The standard Gauss sum of a primitive character has norm square root of r. -/
theorem primitive_gauss_norm {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt r := by
  have h := primitive_gauss_norm_sq χ hχ
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), norm_nonneg (gaussSum χ ZMod.stdAddChar),
    Real.sqrt_nonneg (r : ℝ)]

/-- Fourier inversion of an arbitrary periodic weight on the natural numbers. -/
theorem periodic_inversion {r : ℕ} [NeZero r] (w : ZMod r → ℂ) (n : ℕ) :
    w n = (r : ℂ)⁻¹ * ∑ b : ZMod r,
      ZMod.dft w b * phase (((b.val : ℝ) / r) * n) := by
  calc
    _ = (ZMod.dft.symm (ZMod.dft w)) (n : ZMod r) := by
      rw [LinearEquiv.symm_apply_apply]
    _ = _ := by
      rw [ZMod.invDFT_apply]
      simp only [smul_eq_mul, ← residue_phase]
      congr 1
      apply sum_congr rfl
      intro b _
      exact mul_comm _ _

/-- Twisting by a periodic weight is a weighted average of shifted Fourier sums. -/
theorem fourierSum_periodic (s : Finset ℕ) (g : ℕ → ℂ)
    {r : ℕ} [NeZero r] (w : ZMod r → ℂ) (α : ℝ) :
    fourierSum s (fun n => w n * g n) α =
      (r : ℂ)⁻¹ * ∑ b : ZMod r,
        ZMod.dft w b * fourierSum s g (α + (b.val : ℝ) / r) := by
  have hterm (n : ℕ) : w n * g n * phase (α * n) =
      (r : ℂ)⁻¹ * ∑ b : ZMod r,
        ZMod.dft w b * (g n * phase ((α + (b.val : ℝ) / r) * n)) := by
    rw [periodic_inversion w n]
    simp_rw [add_mul, AddChar.map_add_eq_mul]
    simp_rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro b _
    ring
  change (∑ n ∈ s, w n * g n * phase (α * n)) = _
  simp_rw [hterm]
  rw [← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro b _
  rw [fourierSum, mul_sum]

/-- The Fourier cost of a periodic twist is its average absolute discrete Fourier transform. -/
theorem fourierNorm_periodic (s : Finset ℕ) (g : ℕ → ℂ)
    {r : ℕ} [NeZero r] (w : ZMod r → ℂ) :
    fourierNorm s (fun n => w n * g n) ≤
      ((r : ℝ)⁻¹ * ∑ b : ZMod r, ‖ZMod.dft w b‖) * fourierNorm s g := by
  apply fourierNorm_le
  intro α
  rw [fourierSum_periodic, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (r : ℝ)⁻¹ * ∑ b : ZMod r,
        ‖ZMod.dft w b‖ * fourierNorm s g := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (sum_le_sum fun b _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (fourierSum_le_norm s g _) (norm_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

/-- A primitive character has every discrete Fourier coefficient bounded by square root of r. -/
theorem primitive_dft_bound {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (b : ZMod r) :
    ‖ZMod.dft (χ : ZMod r → ℂ) b‖ ≤ Real.sqrt r := by
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, primitive_gauss_norm χ hχ]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) ((χ⁻¹).norm_le_one _)

/-- Lemma 4.3, page 20, second inequality for a primitive Dirichlet character. -/
theorem fourierNorm_character (s : Finset ℕ) (g : ℕ → ℂ)
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    fourierNorm s (fun n => χ n * g n) ≤ Real.sqrt r * fourierNorm s g := by
  refine (fourierNorm_periodic s g (χ : ZMod r → ℂ)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (fourierNorm_nonneg s g)
  calc
    _ ≤ (r : ℝ)⁻¹ * ∑ _b : ZMod r, Real.sqrt r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun b _ => primitive_dft_bound χ hχ b
    _ = _ := by simp [ZMod.card, nsmul_eq_mul, NeZero.ne (r : ℝ)]

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.dft_conj
#print axioms LeanLab.ChenPrimeExceptional.Task101.primitive_gauss_norm_sq
#print axioms LeanLab.ChenPrimeExceptional.Task101.primitive_gauss_norm
#print axioms LeanLab.ChenPrimeExceptional.Task101.periodic_inversion
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_periodic
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_periodic
#print axioms LeanLab.ChenPrimeExceptional.Task101.primitive_dft_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_character
