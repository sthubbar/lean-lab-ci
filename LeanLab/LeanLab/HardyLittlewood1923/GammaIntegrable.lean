import LeanLab.HardyLittlewood1923.GammaVertical

/-! AI wrote this Lean code for CODEX task52. Kernel integrability for paper P0004 page 11. -/

open Complex Real Set Filter MeasureTheory

namespace LeanLab.HardyLittlewood1923.Task52

lemma integrable_exp_envelope {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) * Real.exp (-δ * |t|)) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0)
      (by norm_num) (by norm_num) hδ
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-δ * t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1)
      (by norm_num) (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => (1 + t) * Real.exp (-δ * t)) (Ioi 0) := by
    convert h0.add h1 using 1
    funext t
    simp only [Pi.add_apply]
    ring
  have hpos : IntegrableOn (fun t : ℝ => (1 + |t|) * Real.exp (-δ * |t|)) (Ioi 0) :=
    hp.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => (1 + |t|) * Real.exp (-δ * |t|)) (Iio 0) := by
    have hp' : IntegrableOn (fun t : ℝ => (1 + t) * Real.exp (-δ * t))
        (Ioi (-(0 : ℝ))) := by simpa only [neg_zero] using hp
    have h := MeasureTheory.IntegrableOn.comp_neg_Iio (c := (0 : ℝ)) hp'
    refine h.congr_fun ?_ measurableSet_Iio
    intro t ht
    dsimp only
    rw [abs_of_neg ht]
  have hneg' := (integrableOn_Iic_iff_integrableOn_Iio).mpr hneg
  rw [← integrableOn_univ, ← (Iic_union_Ioi (a := (0 : ℝ))), integrableOn_union]
  exact ⟨hneg', hpos⟩

/-- Absolute integrability of the Gamma kernel on every line in the strip. -/
theorem gamma_kernel_integrable {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2)
    {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I) *
      z ^ (-((σ : ℂ) + t * I))) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let δ := π / 2 - |Complex.arg z|
  let C := √(2 * π) * Real.exp (5 / 2) * ‖z‖ ^ (-σ) * (5 / 2)
  have hδ : 0 < δ := kernel_decay_pos hz
  have hc : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I) *
      z ^ (-((σ : ℂ) + t * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : ContinuousAt Complex.Gamma ((σ : ℂ) + t * I) := by
      apply DifferentiableAt.continuousAt (𝕜 := ℂ)
      apply Complex.differentiableAt_Gamma
      intro n hn
      have h := congr_arg Complex.re hn
      simp at h
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hl : ContinuousAt (fun u : ℝ => (σ : ℂ) + u * I) t := by fun_prop
    have hp : DifferentiableAt ℂ (fun s : ℂ => z ^ (-s)) ((σ : ℂ) + t * I) :=
      DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hz0)
    exact (hG.comp (f := fun u : ℝ => (σ : ℂ) + u * I) hl).mul
      (hp.continuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * I) hl)
  refine Integrable.mono' ((integrable_exp_envelope hδ).const_mul C)
    hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hg := gamma_kernel_bound (s := (σ : ℂ) + t * I) (by simpa using h1)
    (by simpa using h2) hz0
  have hn : 1 ≤ ‖((σ : ℂ) + t * I) + 1‖ := by
    have h := Complex.re_le_norm (((σ : ℂ) + t * I) + 1)
    simp at h
    linarith
  have hp : ‖((σ : ℂ) + t * I) + 1‖ ^ (σ - 1 / 2) ≤
      (5 / 2) * (1 + |t|) := by
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
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_self, sub_zero, add_zero, add_im, zero_add, mul_im, mul_one] at hg
  calc _ ≤ _ := hg
    _ ≤ C * ((1 + |t|) * Real.exp (-δ * |t|)) := by
      dsimp [C, δ]
      have h := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ √(2 * π) * Real.exp (5 / 2) * ‖z‖ ^ (-σ) *
          Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) by positivity)
      simp only [neg_mul, mul_neg] at h ⊢
      convert h using 1 <;> ring

#print axioms integrable_exp_envelope
#print axioms gamma_kernel_integrable

end LeanLab.HardyLittlewood1923.Task52
