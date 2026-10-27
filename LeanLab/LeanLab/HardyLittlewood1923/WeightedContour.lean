import LeanLab.HardyLittlewood1923.GammaVertical
import LeanLab.HardyLittlewood1923.U1503Explicit

/-!
AI wrote this Lean code for CODEX task52.
Paper P0004 page 8 and page 11 equation 2.416 use the exponential Mellin kernel.
This file proves its finite rectangle shift and bounds its vertical line integrand.
The infinite contour identity for the weighted von Mangoldt series is a separate step.
-/

open Complex Real Set Filter MeasureTheory

namespace LeanLab.HardyLittlewood1923.Task52

/-- The series is absolutely convergent for every positive real part. -/
theorem summable_exponential {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => a n * Complex.exp (-(n : ℂ) * z)) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul 1 hz).of_norm_bounded
  intro n
  have hn : ‖a n‖ ≤ (n : ℝ) :=
    (ha n).trans (ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_self (Nat.cast_nonneg n)))
  rw [norm_mul, Complex.norm_exp]
  have he : (-(n : ℂ) * z).re = -z.re * n := by simp; ring
  rw [he]
  simpa only [pow_one] using mul_le_mul_of_nonneg_right hn (Real.exp_pos (-z.re * n)).le

noncomputable def weightedSum {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
    Complex.exp (-(n : ℂ) * z)

theorem summable_weightedSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
      Complex.exp (-(n : ℂ) * z)) := by
  apply summable_exponential (z := z) (fun n => ?_) hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)

noncomputable def weightedKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
    Complex.Gamma s * z ^ (-s)

lemma weightedKernel_differentiable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {z s : ℂ} (hz : z ≠ 0) (hs : 0 < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (weightedKernel χ z) s := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hD : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    (hLd.analyticAt s).deriv.differentiableAt
  have hG : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have h := congr_arg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (((hD.div (hLd s) hL).neg).mul hG).mul
    (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hz))

/-- The finite contour shift for the exponential Mellin kernel. -/
theorem weighted_rectangle_shift {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {z : ℂ} (hz : z ≠ 0) {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hL : ∀ s ∈ Rectangle ((a : ℂ) - I * T) ((b : ℂ) + I * T),
      DirichletCharacter.LFunction χ s ≠ 0) :
    VIntegral (weightedKernel χ z) b (-T) T = VIntegral (weightedKernel χ z) a (-T) T -
      HIntegral (weightedKernel χ z) a b (-T) + HIntegral (weightedKernel χ z) a b T := by
  have hh : HolomorphicOn (weightedKernel χ z)
      (Rectangle ((a : ℂ) - I * T) ((b : ℂ) + I * T)) := by
    intro s hs
    have hs' := hs
    simp only [Rectangle, Complex.mem_reProdIm] at hs'
    have hre : a ≤ s.re := by
      have h := hs'.1
      simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
        sub_zero, add_re, one_mul, sub_self, add_zero] at h
      rw [Set.uIcc_of_le hab] at h
      exact h.1
    exact (weightedKernel_differentiable hχ hz (by linarith) (hL s hs)).differentiableWithinAt
  have hr := HolomorphicOn.vanishesOnRectangle hh subset_rfl
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
    zero_mul, mul_zero, sub_zero, add_re, one_mul, sub_self, add_zero, sub_im, mul_im,
    add_im, zero_add, zero_sub] at hr
  linear_combination hr

/-- Hypothesis R supplies the nonvanishing needed for the finite shift. -/
theorem weighted_rectangle_shift_of_noZeros {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    {z : ℂ} (hz : z ≠ 0) {a b T : ℝ} (ha : 0 < a) (hΘ : Θ < a) (hab : a ≤ b) :
    VIntegral (weightedKernel χ z) b (-T) T = VIntegral (weightedKernel χ z) a (-T) T -
      HIntegral (weightedKernel χ z) a b (-T) + HIntegral (weightedKernel χ z) a b T := by
  have hn := U1503.ne_one_of_primitive hχ hq
  apply weighted_rectangle_shift hn hz ha hab
  intro s hs
  have hs' := hs
  simp only [Rectangle, Complex.mem_reProdIm] at hs'
  have hre : a ≤ s.re := by
    have h := hs'.1
    simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
      sub_zero, add_re, one_mul, sub_self, add_zero] at h
    rw [Set.uIcc_of_le hab] at h
    exact h.1
  by_cases hs1 : s = 1
  · subst s
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hn) (by simp)
  · exact hZ q χ hχ s (by linarith) hs1

/-- The vertical integrand bound uses the proved logarithmic derivative bound. -/
theorem weightedKernel_bound {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {η σ t : ℝ} (hη : 0 < η) (hσ : Θ + η ≤ σ) (h1 : 1 / 2 ≤ σ)
    (h2 : σ ≤ 3 / 2) (hs1 : (σ : ℂ) + t * I ≠ 1) {z : ℂ} (hz : z ≠ 0) :
    ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ ≤
      ((U1503.KW + 1 / (U1503.lZ * η)) *
          Real.log (60 * q * (|t| + 4) ^ 2 * LeanLab.PNTPort.DirichletZF.Z) +
          ‖(σ : ℂ) + t * I - 1‖⁻¹) *
        (√(2 * π) * Real.exp (5 / 2) * ‖z‖ ^ (-σ) *
          ‖((σ : ℂ) + t * I) + 1‖ ^ (σ - 1 / 2) *
            Real.exp (-((π / 2 - |Complex.arg z|) * |t|))) := by
  have hD := U1503.logDeriv_region hZ hχ hη hσ h1 (by linarith) hs1
  have hG := gamma_kernel_bound (s := (σ : ℂ) + t * I)
    (by simpa using h1) (by simpa using h2) hz
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_self, sub_zero, add_zero, add_im, zero_add, mul_im, mul_one] at hG
  have he : ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ =
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ *
          ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ := by
    simp [weightedKernel, norm_mul, mul_assoc]
  rw [he]
  exact mul_le_mul hD hG (norm_nonneg _) ((norm_nonneg _).trans hD)

#print axioms summable_exponential
#print axioms summable_weightedSum
#print axioms weightedKernel_differentiable
#print axioms weighted_rectangle_shift
#print axioms weighted_rectangle_shift_of_noZeros
#print axioms weightedKernel_bound

end LeanLab.HardyLittlewood1923.Task52
