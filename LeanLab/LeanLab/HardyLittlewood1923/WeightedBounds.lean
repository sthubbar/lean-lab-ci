import LeanLab.HardyLittlewood1923.ExponentialDecay

/-!
AI wrote this Lean code for CODEX task52.
These polynomial envelopes justify the limiting contour on P0004 page 11 after equation 2.416.
The sharp Gamma exponent is retained in GammaVertical for later quantitative estimates.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open LeanLab.HardyLittlewood1923.U1503 (KW lZ KW_pos lZ_pos logDeriv_region)
open LeanLab.PNTPort.DirichletZF (Z Z_pos)

namespace LeanLab.HardyLittlewood1923.Task52

lemma rpow_strip {x σ : ℝ} (hx : 0 < x) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) :
    x ^ (-σ) ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 2 : ℝ)) := by
  rcases le_total 1 x with hx1 | hx1
  · have hp := Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg h1)
    linarith [Real.rpow_nonneg hx.le (-(3 / 2 : ℝ))]
  · have hp := Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg h2)
    linarith [Real.rpow_nonneg hx.le (-(1 / 2 : ℝ))]

lemma norm_line_add_one_power {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) (t : ℝ) :
    ‖((σ : ℂ) + t * I) + 1‖ ^ (σ - 1 / 2) ≤ (5 / 2) * (1 + |t|) := by
  have hn : 1 ≤ ‖((σ : ℂ) + t * I) + 1‖ := by
    have h := Complex.re_le_norm (((σ : ℂ) + t * I) + 1)
    simp at h
    linarith
  calc _ ≤ ‖((σ : ℂ) + t * I) + 1‖ ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ = ‖((σ : ℂ) + t * I) + 1‖ := Real.rpow_one _
    _ ≤ (5 / 2) * (1 + |t|) := by
      have he : ((σ : ℂ) + t * I) + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [he]
      calc _ ≤ ‖((σ + 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = σ + 1 + |t| := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ σ + 1),
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := by nlinarith [abs_nonneg t]

lemma gamma_kernel_uniform {z : ℂ} (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ ≤
        C * (1 + |t|) * Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let B := ‖z‖ ^ (-(1 / 2 : ℝ)) + ‖z‖ ^ (-(3 / 2 : ℝ))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨√(2 * π) * Real.exp (5 / 2) * B * (5 / 2), by positivity,
    fun σ h1 h2 t => ?_⟩
  have hp : ‖z‖ ^ (-σ) ≤ B := rpow_strip hzn h1 h2
  have hl := norm_line_add_one_power h1 h2 t
  have hg := gamma_kernel_bound (s := (σ : ℂ) + t * I) (by simpa using h1)
    (by simpa using h2) hz0
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_self, add_zero, add_im, zero_add, mul_im, mul_one] at hg
  calc _ ≤ _ := hg
    _ ≤ √(2 * π) * Real.exp (5 / 2) * B * ((5 / 2) * (1 + |t|)) *
        Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hl
        (by positivity) (by positivity)
    _ = _ := by ring

lemma logDeriv_polynomial_bound {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {η σ t : ℝ} (hη : 0 < η) (hσ : Θ + η ≤ σ) (h1 : 1 / 2 ≤ σ)
    (h2 : σ ≤ 3 / 2) (hs1 : (σ : ℂ) + t * I ≠ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤
      (KW + 1 / (lZ * η)) * (960 * q * Z) * (1 + |t|) ^ 2 +
        ‖(σ : ℂ) + t * I - 1‖⁻¹ := by
  have hK := KW_pos
  have hl := lZ_pos
  have hZp := Z_pos
  have hsq : (|t| + 4) ^ 2 ≤ 16 * (1 + |t|) ^ 2 := by
    nlinarith [abs_nonneg t, sq_nonneg |t|]
  have hlog : Real.log (60 * q * (|t| + 4) ^ 2 * Z) ≤ (960 * q * Z) * (1 + |t|) ^ 2 := by
    calc _ ≤ 60 * q * (|t| + 4) ^ 2 * Z := Real.log_le_self (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 60 * q * Z by positivity)
        convert h using 1 <;> ring
  refine (logDeriv_region hZ hχ hη hσ h1 (by linarith) hs1).trans ?_
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ KW + 1 / (lZ * η) by positivity)
  have h' : (KW + 1 / (lZ * η)) * Real.log (60 * q * (|t| + 4) ^ 2 * Z) ≤
      (KW + 1 / (lZ * η)) * (960 * q * Z) * (1 + |t|) ^ 2 := by
    convert h using 1 <;> ring
  linarith only [h']

#print axioms rpow_strip
#print axioms norm_line_add_one_power
#print axioms gamma_kernel_uniform
#print axioms logDeriv_polynomial_bound

end LeanLab.HardyLittlewood1923.Task52
