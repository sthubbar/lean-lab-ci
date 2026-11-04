import LeanLab.ExceptionalSet.WeightedGallagher264

/-
Interval correlation and the squared sinc Fourier kernel.
Source: Brudern and Perelli 1998, page 356 display 3.
AI wrote the Lean code. Goldbach is open.
-/

open MeasureTheory FourierTransform
open scoped ComplexConjugate ENNReal

namespace LeanLab.ExceptionalSet.TriangleKernel264

/-- Plancherel preserves the integral inner product on L1 intersect L2. -/
theorem integral_inner_fourier (f g : ℝ → ℂ) (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    ∫ t : ℝ, inner ℂ (𝓕 f t) (𝓕 g t) = ∫ x : ℝ, inner ℂ (f x) (g x) := by
  calc
    _ = ∫ t : ℝ, inner ℂ ((𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) t)
        ((𝓕 (hg₂.toLp g) : Lp ℂ 2 volume) t) := by
      apply integral_congr_ae
      filter_upwards [WindowParseval264.fourierIntegral_ae_eq f hf₁ hf₂,
        WindowParseval264.fourierIntegral_ae_eq g hg₁ hg₂] with t ht ht'
      rw [ht, ht']
    _ = inner ℂ (𝓕 (hf₂.toLp f)) (𝓕 (hg₂.toLp g)) := (L2.inner_def _ _).symm
    _ = inner ℂ (hf₂.toLp f) (hg₂.toLp g) := Lp.inner_fourier_eq _ _
    _ = ∫ x : ℝ, inner ℂ ((hf₂.toLp f) x) ((hg₂.toLp g) x) := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hx hx'
      rw [hx, hx']

/-- The unit interval centred at zero. -/
noncomputable def box : ℝ → ℂ := (Set.Ico (-1 / 2 : ℝ) (1 / 2)).indicator (fun _ => 1)

/-- The centred unit interval indicator is in every Lp space. -/
theorem box_memLp (p : ℝ≥0∞) : MemLp box p :=
  memLp_indicator_const p measurableSet_Ico.nullMeasurableSet 1 (Or.inr (by simp))

/-- The Fourier integral of the centred unit interval is sinc. -/
theorem fourier_box (t : ℝ) : 𝓕 box t = (Real.sinc (Real.pi * t) : ℂ) := by
  rw [box, WindowParseval264.fourier_interval _ _ (by norm_num) 1 t, mul_one]
  have he (x : ℝ) : Complex.exp ((-2 * Real.pi * t * Complex.I) * x) =
      Complex.exp (((-2 * Real.pi * t) * x : ℝ) * Complex.I) := by
    congr 1
    push_cast
    ring
  simp_rw [he]
  by_cases ht : t = 0
  · subst t
    norm_num
  · have hc : -2 * Real.pi * t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht
    rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Complex.exp (x * Complex.I)) hc]
    have ha : -2 * Real.pi * t * (-1 / 2) = -(-Real.pi * t) := by ring
    have hb : -2 * Real.pi * t * (1 / 2) = -Real.pi * t := by ring
    rw [ha, hb, integral_exp_mul_I_eq_sinc]
    have hs : Real.sinc (-Real.pi * t) = Real.sinc (Real.pi * t) := by
      rw [neg_mul, Real.sinc_neg]
    rw [hs]
    rw [Complex.real_smul]
    push_cast
    field_simp [ht, Real.pi_ne_zero]

/-- The correlation of two unit interval indicators is the triangle function. -/
theorem box_correlation (y : ℝ) :
    (∫ x : ℝ, inner ℂ (box x) (box (x - y))) = (max 0 (1 - |y|) : ℝ) := by
  let I : Set ℝ := Set.Ico (-1 / 2) (1 / 2)
  let J : Set ℝ := Set.Ico (y - 1 / 2) (y + 1 / 2)
  have he : (fun x : ℝ => inner ℂ (box x) (box (x - y))) =
      (I ∩ J).indicator (fun _ => (1 : ℂ)) := by
    funext x
    have ht : x - y ∈ I ↔ x ∈ J := by
      dsimp [I, J]
      simp only [Set.mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    change inner ℂ (I.indicator (fun _ => (1 : ℂ)) x)
      (I.indicator (fun _ => (1 : ℂ)) (x - y)) = _
    by_cases hx : x ∈ I <;> by_cases hy : x ∈ J <;>
      simp [Set.indicator, Set.mem_inter_iff, ht, hx, hy]
  rw [he]
  dsimp [I, J]
  rw [Set.Ico_inter_Ico, integral_indicator_const 1 measurableSet_Ico,
    Real.volume_real_Ico, Complex.real_smul, mul_one]
  congr 1
  change max (min (1 / 2 : ℝ) (y + 1 / 2) - max (-1 / 2 : ℝ) (y - 1 / 2)) 0 = _
  by_cases hy : 0 ≤ y
  · rw [min_eq_left (show (1 / 2 : ℝ) ≤ y + 1 / 2 by linarith),
      max_eq_right (show (-1 / 2 : ℝ) ≤ y - 1 / 2 by linarith), abs_of_nonneg hy, max_comm]
    congr 1
    ring
  · rw [min_eq_right (show y + 1 / 2 ≤ (1 / 2 : ℝ) by linarith),
      max_eq_left (show y - 1 / 2 ≤ (-1 / 2 : ℝ) by linarith), abs_of_nonpos (le_of_not_ge hy),
      max_comm]
    congr 1
    ring

/-- The Fourier integral of squared sinc is the compactly supported triangle. -/
theorem fourier_sinc_sq (y : ℝ) :
    𝓕 (fun t : ℝ => ((Real.sinc (Real.pi * t)) ^ 2 : ℝ) : ℝ → ℂ) y =
      (max 0 (1 - |y|) : ℝ) := by
  have hf₁ : Integrable box := memLp_one_iff_integrable.mp (box_memLp 1)
  have hg₁ : Integrable (fun x : ℝ => box (x - y)) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using hf₁.comp_add_right (-y)
  have hg₂ : MemLp (fun x : ℝ => box (x - y)) 2 := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (box_memLp 2).comp_measurePreserving (measurePreserving_add_right volume (-y))
  have hp := integral_inner_fourier box (fun x => box (x - y)) hf₁ (box_memLp 2) hg₁ hg₂
  rw [box_correlation] at hp
  have htrans (t : ℝ) : 𝓕 (fun x : ℝ => box (x - y)) t =
      Complex.exp ((-2 * Real.pi * t * Complex.I) * y) * (Real.sinc (Real.pi * t) : ℂ) := by
    simpa only [Finset.sum_singleton, one_mul, fourier_box] using
      WeightedGallagher264.fourier_sum_translates ({()} : Finset Unit) (fun _ => y)
        (fun _ => 1) box hf₁ t
  calc
    _ = ∫ t : ℝ, inner ℂ (𝓕 box t) (𝓕 (fun x : ℝ => box (x - y)) t) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with t
      rw [fourier_box, htrans]
      have he : Complex.exp (↑(-2 * Real.pi * t * y) * Complex.I) =
          Complex.exp ((-2 * Real.pi * t * Complex.I) * y) := by
        congr 1
        push_cast
        ring
      rw [he]
      simp only [smul_eq_mul, RCLike.inner_apply, Complex.conj_ofReal]
      push_cast
      ring
    _ = _ := hp

/-- Squared sinc is integrable on the real line. -/
theorem sinc_sq_integrable :
    Integrable (fun t : ℝ => ((Real.sinc (Real.pi * t)) ^ 2 : ℝ) : ℝ → ℂ) := by
  have hf₁ : Integrable box := memLp_one_iff_integrable.mp (box_memLp 1)
  have hF := WindowParseval264.fourierIntegral_memLp box hf₁ (box_memLp 2)
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hr : Integrable (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
    convert hi using 1
    funext t
    rw [fourier_box]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact hr.ofReal

/-- The normalized squared sinc has integral one. -/
theorem integral_sinc_sq : (∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2) = 1 := by
  have h := fourier_sinc_sq 0
  simp only [Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul,
    Complex.ofReal_zero, Complex.exp_zero, one_smul, abs_zero, sub_zero,
    max_eq_right zero_le_one, Complex.ofReal_one] at h
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  rw [← integral_re sinc_sq_integrable] at hr
  change (∫ t : ℝ, ((Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ).re) = 1 at hr
  simpa only [Complex.ofReal_re] using hr

/-- Positive real dilation rescales the Fourier integral. -/
theorem fourier_comp_pos_mul (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (y : ℝ) :
    𝓕 (fun x => f (c * x)) y = (c⁻¹ : ℂ) * 𝓕 f (y / c) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * y) * Complex.I) * f (c * x)) =
      (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * (y / c)) * Complex.I) * f x) ∘
        (fun x : ℝ => c * x) := by
    funext x
    change Complex.exp (↑(-2 * Real.pi * x * y) * Complex.I) * f (c * x) =
      Complex.exp (↑(-2 * Real.pi * (c * x) * (y / c)) * Complex.I) * f (c * x)
    have hex : -2 * Real.pi * x * y = -2 * Real.pi * (c * x) * (y / c) := by
      field_simp
    rw [hex]
  rw [he]
  have hs := Measure.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * (y / c)) * Complex.I) * f x) c
  simpa only [Function.comp_def, abs_of_pos (inv_pos.mpr hc), Complex.real_smul,
    Complex.ofReal_inv] using hs

/-- The Fourier integral of a positively dilated squared sinc is a dilated triangle. -/
theorem fourier_scaled_sinc_sq {c : ℝ} (hc : 0 < c) (y : ℝ) :
    𝓕 (fun t : ℝ => ((Real.sinc (Real.pi * (c * t))) ^ 2 : ℝ) : ℝ → ℂ) y =
      (c⁻¹ * max 0 (1 - |y / c|) : ℝ) := by
  have hs := fourier_comp_pos_mul
    (fun t : ℝ => ((Real.sinc (Real.pi * t)) ^ 2 : ℝ) : ℝ → ℂ) hc y
  rw [fourier_sinc_sq] at hs
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv] using hs

end LeanLab.ExceptionalSet.TriangleKernel264
