/-
P0022, Kaniecki 1995, the kernel integral (9), p. 365, for every `A ≥ 0`, PROVED.
PC run 20261021T0604Z-1697, unit U-1368, T1.

`Kernel9A` of Lemma5Bound21.lean, the paper's (9):
`∫_0^∞ |(e^{δ(σ+it)} - 1)/(σ+it)|² cos(At) dt = 0` for `A ≥ δ` and
`= π/(2σ) (e^{σ(2δ-A)} - e^{σA})` for `0 ≤ A < δ`.
Proof, contour free:
1. the Fourier transform of `e^{-σ|v|}` is `2σ/(σ² + t²)`, by splitting at `0` and
   integrating complex exponentials, as in ChirreHagen2025/SmoothKernel.lean;
2. Fourier inversion, `Continuous.fourierInv_fourier_eq`, and `t = 2πw`, give
   `∫_ℝ cos(Bt)/(σ² + t²) dt = π e^{-σ|B|}/σ`, and by evenness the half line integral is
   `π e^{-σ|B|}/(2σ)`, `cosLor`;
3. `|e^{δs} - 1|² = e^{2δσ} + 1 - 2 e^{δσ} cos(δt)` and `2 cos(δt) cos(At) =
   cos((δ+A)t) + cos((δ-A)t)` reduce (9) to three instances of 2; the exponentials combine
   to `e^{σ(2δ-A)} - e^{σ(δ - |δ-A|)}`, which is `κ(A)` in both cases.
Then `bound21_of_near`: inequality (21) CONDITIONAL ON `Near21` only.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Bound21

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

/-! ### The Fourier transform of `e^{-σ|v|}` -/

/-- `e^{-σ|v|} e^{itv}`. -/
noncomputable def gS (σ t v : ℝ) : ℂ := Complex.exp (((-σ * |v| : ℝ) : ℂ) + (t : ℂ) * v * Complex.I)

theorem gS_Iic {σ t v : ℝ} (hv : v ≤ 0) : gS σ t v = Complex.exp ((σ + t * Complex.I) * v) := by
  unfold gS; congr 1; rw [abs_of_nonpos hv]; push_cast; ring

theorem gS_Ioi {σ t v : ℝ} (hv : 0 < v) : gS σ t v = Complex.exp ((-σ + t * Complex.I) * v) := by
  unfold gS; congr 1; rw [abs_of_pos hv]; push_cast; ring

theorem gS_intIic {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : IntegrableOn (gS σ t) (Iic 0) := by
  have h := integrableOn_exp_mul_complex_Iic (a := (σ : ℂ) + t * Complex.I) (by simpa using hσ) 0
  exact h.congr_fun (fun v hv => (gS_Iic hv).symm) measurableSet_Iic

theorem gS_intIoi {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : IntegrableOn (gS σ t) (Ioi 0) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -(σ : ℂ) + t * Complex.I) (by simpa using hσ) 0
  exact h.congr_fun (fun v hv => (gS_Ioi hv).symm) measurableSet_Ioi

theorem integrable_gS {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : Integrable (gS σ t) := by
  have := (gS_intIic hσ t).union (gS_intIoi hσ t)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- `∫ e^{-σ|v|} e^{itv} dv = 2σ/(σ² + t²)`. -/
theorem integral_gS {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∫ v, gS σ t v = ((2 * σ / (σ ^ 2 + t ^ 2) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (gS_intIic hσ t) (gS_intIoi hσ t)]
  rw [setIntegral_congr_fun measurableSet_Iic (fun v hv => gS_Iic hv),
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => gS_Ioi hv)]
  rw [integral_exp_mul_complex_Iic (by simpa using hσ),
    integral_exp_mul_complex_Ioi (by simpa using hσ)]
  have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (-(σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h4 : ((σ : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < σ ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  have e : ((σ : ℂ) ^ 2 + (t : ℂ) ^ 2) = -((-(σ : ℂ) + t * Complex.I) * (σ + t * Complex.I)) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [e] at h4 ⊢
  field_simp
  ring

/-! ### Fourier inversion: `∫_ℝ cos(Bt)/(σ² + t²) dt = π e^{-σ|B|}/σ` -/

/-- `e^{-σ|v|}` as a complex function. -/
noncomputable def fS (σ : ℝ) (v : ℝ) : ℂ := ((Real.exp (-σ * |v|) : ℝ) : ℂ)

theorem fourier_fS {σ : ℝ} (hσ : 0 < σ) (w : ℝ) :
    𝓕 (fS σ) w = ((2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_gS hσ (-2 * π * w)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [fS, gS, smul_eq_mul]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem integrable_lor {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun t : ℝ => 1 / (σ ^ 2 + t ^ 2) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hσ.ne')).const_mul (σ⁻¹ ^ 2)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only
  field_simp

theorem integrable_FS {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun w : ℝ => 2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) := by
  have h := ((integrable_lor hσ).comp_mul_left' (by positivity : (-2 * π) ≠ 0)).const_mul (2 * σ)
  refine h.congr (ae_of_all _ fun w => ?_)
  simp only
  rw [mul_one_div]

theorem integrable_fourier_fS {σ : ℝ} (hσ : 0 < σ) : Integrable (𝓕 (fS σ)) := by
  have h' := (integrable_FS hσ).ofReal (𝕜 := ℂ)
  exact h'.congr (ae_of_all _ fun w => (fourier_fS hσ w).symm)

theorem continuous_fS (σ : ℝ) : Continuous (fS σ) := by
  unfold fS; fun_prop

theorem integrable_fS {σ : ℝ} (hσ : 0 < σ) : Integrable (fS σ) := by
  have h := (integrable_gS hσ 0).norm
  refine (h.ofReal (𝕜 := ℂ)).congr (ae_of_all _ fun v => ?_)
  simp only [fS, gS]
  rw [Complex.norm_exp]
  congr 2
  simp

/-- The real form of inversion: `∫_ℝ cos(2π w x) 2σ/(σ² + (2πw)²) dw = e^{-σ|x|}`. -/
theorem inv_fS {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    ∫ w : ℝ, Real.cos (2 * π * w * x) * (2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2)) =
      Real.exp (-σ * |x|) := by
  have hinv := congrFun ((continuous_fS σ).fourierInv_fourier_eq (integrable_fS hσ)
    (integrable_fourier_fS hσ)) x
  have hF : 𝓕 (fS σ) = fun w => ((2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) : ℝ) : ℂ) :=
    funext (fourier_fS hσ)
  rw [hF, Real.fourierInv_eq'] at hinv
  have hint : Integrable fun w : ℝ =>
      Complex.exp (↑(2 * π * ⟪w, x⟫) * Complex.I) •
        ((2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) : ℝ) : ℂ) := by
    refine (integrable_FS hσ).mono' ?_ (ae_of_all _ fun w => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.smul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const))
        (Complex.continuous_ofReal.comp ?_)
      refine continuous_const.div (by fun_prop) fun w => ?_
      positivity
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
  have hre := congrArg Complex.re hinv
  have h2 : ∫ w : ℝ, (Complex.exp (↑(2 * π * ⟪w, x⟫) * Complex.I) •
        ((2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) : ℝ) : ℂ)).re =
      (∫ w : ℝ, Complex.exp (↑(2 * π * ⟪w, x⟫) * Complex.I) •
        ((2 * σ / (σ ^ 2 + (-2 * π * w) ^ 2) : ℝ) : ℂ)).re := integral_re hint
  rw [← h2] at hre
  simp only [fS, Complex.ofReal_re] at hre
  rw [← hre]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [smul_eq_mul, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  congr 2
  simp
  ring

/-- `∫_ℝ cos(Bt)/(σ² + t²) dt = (π/σ) e^{-σ|B|}`. -/
theorem cosLorR {σ : ℝ} (hσ : 0 < σ) (B : ℝ) :
    ∫ t : ℝ, Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) = π / σ * Real.exp (-σ * |B|) := by
  have h1 := inv_fS hσ B
  have h2 := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => Real.cos (B * t) * (2 * σ * (1 / (σ ^ 2 + t ^ 2)))) (2 * π)
  have hpi : 0 < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.2 hpi), smul_eq_mul] at h2
  have h3 : ∫ w : ℝ, Real.cos (B * (2 * π * w)) * (2 * σ * (1 / (σ ^ 2 + (2 * π * w) ^ 2))) =
      Real.exp (-σ * |B|) := by
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    rw [show B * (2 * π * w) = 2 * π * w * B by ring, show (-2 * π * w) ^ 2 = (2 * π * w) ^ 2 by
      ring, mul_one_div]
  rw [h3] at h2
  have h4 : ∫ t : ℝ, Real.cos (B * t) * (2 * σ * (1 / (σ ^ 2 + t ^ 2))) =
      2 * σ * ∫ t : ℝ, Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only; ring
  rw [h4] at h2
  have hσ' : σ ≠ 0 := hσ.ne'
  have hπ' : π ≠ 0 := Real.pi_pos.ne'
  field_simp at h2 ⊢
  linarith

theorem integrable_cosLor {σ : ℝ} (hσ : 0 < σ) (B : ℝ) :
    Integrable fun t : ℝ => Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) := by
  refine (integrable_lor hσ).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (by positivity) (abs_cos_le_one _)

/-- **`∫_0^∞ cos(Bt)/(σ² + t²) dt = π e^{-σ|B|}/(2σ)`**, by evenness. -/
theorem cosLor {σ : ℝ} (hσ : 0 < σ) (B : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) =
      π / (2 * σ) * Real.exp (-σ * |B|) := by
  have hI := integrable_cosLor hσ B
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hI.integrableOn hI.integrableOn
  have hneg : ∫ t in Iic (0 : ℝ), Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) =
      ∫ t in Ioi (0 : ℝ), Real.cos (B * t) * (1 / (σ ^ 2 + t ^ 2)) := by
    rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    rw [mul_neg, Real.cos_neg, neg_sq]
  rw [hneg, cosLorR hσ B] at hsplit
  have hσ' : σ ≠ 0 := hσ.ne'
  have e : π / (2 * σ) * Real.exp (-σ * |B|) = (π / σ * Real.exp (-σ * |B|)) / 2 := by
    field_simp
  rw [e, ← hsplit]
  ring

/-! ### The kernel as a cosine polynomial over `σ² + t²` -/

theorem kern_eq (T σ t : ℝ) :
    kern T σ t = (Real.exp (dl T * σ) ^ 2 + 1 - 2 * Real.exp (dl T * σ) * Real.cos (dl T * t)) *
      (1 / (σ ^ 2 + t ^ 2)) := by
  unfold kern
  rw [show Real.log (1 + 1 / T) = dl T from rfl]
  generalize dl T = d
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add_mul_I,
    Complex.normSq_apply]
  have hz : (↑d * (↑σ + ↑t * Complex.I) : ℂ) = ↑(d * σ) + ↑(d * t) * Complex.I := by
    push_cast; ring
  rw [hz]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_re,
    Complex.exp_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add, sub_zero]
  rw [div_eq_mul_one_div]
  congr 1
  linear_combination Real.exp (d * σ) ^ 2 * Real.sin_sq_add_cos_sq (d * t)

theorem kern_mul_cos (T σ A t : ℝ) :
    kern T σ t * Real.cos (A * t) =
      (Real.exp (dl T * σ) ^ 2 + 1) * (Real.cos (A * t) * (1 / (σ ^ 2 + t ^ 2))) -
        Real.exp (dl T * σ) * (Real.cos ((dl T + A) * t) * (1 / (σ ^ 2 + t ^ 2))) -
        Real.exp (dl T * σ) * (Real.cos ((dl T - A) * t) * (1 / (σ ^ 2 + t ^ 2))) := by
  rw [kern_eq]
  have hc : Real.cos ((dl T + A) * t) + Real.cos ((dl T - A) * t) =
      2 * Real.cos (dl T * t) * Real.cos (A * t) := by
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]; ring
  linear_combination (Real.exp (dl T * σ) * (1 / (σ ^ 2 + t ^ 2))) * hc

/-- **(9), p. 365, PROVED**: `Kernel9A`. -/
theorem kernel9A : Kernel9A := by
  intro T σ A hT hσ hA
  have i0 := integrable_cosLor hσ A
  have i1 := integrable_cosLor hσ (dl T + A)
  have i2 := integrable_cosLor hσ (dl T - A)
  have hd := dl_pos hT
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => kern_mul_cos T σ A t]
  set E := Real.exp (dl T * σ)
  have j0 : IntegrableOn (fun t => (E ^ 2 + 1) * (Real.cos (A * t) * (1 / (σ ^ 2 + t ^ 2))))
    (Ioi 0) := (i0.const_mul _).integrableOn
  have j1 : IntegrableOn (fun t => E * (Real.cos ((dl T + A) * t) * (1 / (σ ^ 2 + t ^ 2))))
    (Ioi 0) := (i1.const_mul _).integrableOn
  have j2 : IntegrableOn (fun t => E * (Real.cos ((dl T - A) * t) * (1 / (σ ^ 2 + t ^ 2))))
    (Ioi 0) := (i2.const_mul _).integrableOn
  have j01 : IntegrableOn (fun t => (E ^ 2 + 1) * (Real.cos (A * t) * (1 / (σ ^ 2 + t ^ 2))) -
    E * (Real.cos ((dl T + A) * t) * (1 / (σ ^ 2 + t ^ 2)))) (Ioi 0) := j0.sub j1
  rw [integral_sub j01 j2, integral_sub j0 j1, integral_const_mul, integral_const_mul,
    integral_const_mul,
    cosLor hσ, cosLor hσ, cosLor hσ, abs_of_nonneg hA, abs_of_pos (by linarith : 0 < dl T + A)]
  have e1 : E ^ 2 * Real.exp (-σ * A) = Real.exp (σ * (2 * dl T - A)) := by
    simp only [E]; rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e2 : E * Real.exp (-σ * (dl T + A)) = Real.exp (-σ * A) := by
    simp only [E]; rw [← Real.exp_add]; congr 1; ring
  unfold kap
  split_ifs with h
  · rw [abs_of_nonpos (by linarith : dl T - A ≤ 0)]
    have e3 : E * Real.exp (-σ * -(dl T - A)) = Real.exp (σ * (2 * dl T - A)) := by
      simp only [E]; rw [← Real.exp_add]; congr 1; ring
    linear_combination π / (2 * σ) * (e1 - e2 - e3)
  · rw [not_le] at h
    rw [abs_of_pos (by linarith : 0 < dl T - A)]
    have e3 : E * Real.exp (-σ * (dl T - A)) = Real.exp (σ * A) := by
      simp only [E]; rw [← Real.exp_add]; congr 1; ring
    linear_combination π / (2 * σ) * (e1 - e2 - e3)

/-- **(21), p. 370**, CONDITIONAL ON `Near21` only; (9) is now PROVED. -/
theorem bound21_of_near (hN : Near21) : Bound21 := bound21_of kernel9A hN

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `Near21`, `Const4`. -/
theorem lemma5_of_near (h4 : Lemma4) (hP : Parseval1920) (hN : Near21) (hC : Const4) :
    Lemma5 :=
  lemma5_of_21 h4 hP kernel9A hN hC

/-- Vacuity: the hypotheses of `Kernel9A` are satisfiable and the right side is not
trivially zero, `κ(0) > 0` at `T = 10`, `σ = 0.6`. -/
theorem kernel9A_nonvacuous :
    0 < kap 10 0.6 0 ∧ ∫ t in Ioi (0 : ℝ), kern 10 0.6 t * Real.cos (0 * t) = kap 10 0.6 0 := by
  refine ⟨?_, kernel9A 10 0.6 0 (by norm_num) (by norm_num) le_rfl⟩
  have hd := dl_pos (by norm_num : (0 : ℝ) < 10)
  unfold kap
  rw [if_neg (not_le.2 hd)]
  refine mul_pos (by positivity) (sub_pos.2 (Real.exp_lt_exp.2 ?_))
  nlinarith

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.integral_gS
#print axioms LeanLab.Kaniecki1995.L5.fourier_fS
#print axioms LeanLab.Kaniecki1995.L5.integrable_fourier_fS
#print axioms LeanLab.Kaniecki1995.L5.inv_fS
#print axioms LeanLab.Kaniecki1995.L5.cosLorR
#print axioms LeanLab.Kaniecki1995.L5.cosLor
#print axioms LeanLab.Kaniecki1995.L5.kern_eq
#print axioms LeanLab.Kaniecki1995.L5.kern_mul_cos
#print axioms LeanLab.Kaniecki1995.L5.kernel9A
#print axioms LeanLab.Kaniecki1995.L5.bound21_of_near
#print axioms LeanLab.Kaniecki1995.L5.lemma5_of_near
#print axioms LeanLab.Kaniecki1995.L5.kernel9A_nonvacuous
