/-
P0022, Kaniecki 1995, the kernel integral behind (22), p. 370, made explicit.
PC run 20261021T0303Z-27628, unit U-1340, T1.

`Kernel9` of Lemma5Bound22.lean is the classical integral (9) at `A = 0`, p. 365. It was a
CITED input. Here it is replaced by a PROVED upper bound for the same integral,
`lintegral_kern_le`:
  `∫_0^∞ |(e^{δs} - 1)/s|² dt ≤ (e^{δσ} - 1)² π/(2σ) + π δ e^{δσ}`,  `s = σ + it`, `e^δ = 1 + 1/T`,
from the pointwise identity `|e^{δs} - 1|² = (e^{δσ} - 1)² + 4 e^{δσ} sin²(δt/2)`, the bound
`σ² + t² ≥ t²` in the second term, the Lorentz integral `∫_0^∞ dt/(σ² + t²) = π/(2σ)` and the
integral `∫_0^∞ sinc² = π/2`. The last comes from the Dirichlet integral, already PROVED in
PNTPort/Perron/Sinc.lean, through the antiderivative `Gs x = ∫_0^{2x} sinc - sin x · sinc x`.

The bound is a little weaker than (9), by a factor `1 + O(σ/T)`, so it does not give the printed
constant `4.51` from `K² < 4.51` alone. It does give (22) from `K² ≤ 4`, `bound22_of_K4`, and
`K² ≈ 2.9635`, so `Const4` holds with room to spare. Result: Lemma 5 CONDITIONAL ON Lemma 4,
`Parseval1920`, `Bound21` and the numerical constant `Const4`; `Kernel9` is no longer used.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Bound22
import LeanLab.PNTPort.Perron.Sinc

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real MeasureTheory Set Filter
open scoped Topology

/-! ### `∫_0^∞ sinc² = π/2` from the Dirichlet integral -/

theorem sin_mul_sinc (x : ℝ) : Real.sin x * sinc x = Real.sin x ^ 2 / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx]; ring

/-- Antiderivative of `sinc²` on `(0, ∞)`. -/
noncomputable def Gs (x : ℝ) : ℝ := (∫ u in (0 : ℝ)..(2 * x), sinc u) - Real.sin x * sinc x

theorem Gs_zero : Gs 0 = 0 := by simp [Gs]

theorem continuous_Gs : Continuous Gs := by
  have hF : Continuous fun y : ℝ => ∫ u in (0 : ℝ)..y, sinc u :=
    continuous_iff_continuousAt.2 fun y =>
      (continuous_sinc.integral_hasStrictDerivAt 0 y).hasDerivAt.continuousAt
  exact (hF.comp (continuous_const.mul continuous_id : Continuous fun x : ℝ => 2 * x)).sub (continuous_sin.mul continuous_sinc)

theorem hasDerivAt_Gs {x : ℝ} (hx : 0 < x) : HasDerivAt Gs (sinc x ^ 2) x := by
  have hF : HasDerivAt (fun y => ∫ u in (0 : ℝ)..y, sinc u) (sinc (2 * x)) (2 * x) :=
    (continuous_sinc.integral_hasStrictDerivAt 0 (2 * x)).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h1 := hF.comp x h2
  have h3 := ((hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx.ne'
  have h := h1.sub h3
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · rw [sinc_of_ne_zero hx.ne', sinc_of_ne_zero (by positivity : (2 * x) ≠ 0), sin_two_mul]
    have hx' : x ≠ 0 := hx.ne'
    norm_num
    field_simp
    ring
  · simp only [Gs, sin_mul_sinc]
    rfl

theorem tendsto_Gs : Tendsto Gs atTop (𝓝 (π / 2)) := by
  have h1 : Tendsto (fun x : ℝ => ∫ u in (0 : ℝ)..(2 * x), sinc u) atTop (𝓝 (π / 2)) :=
    LeanLab.PNTPort.Perron.tendsto_intervalIntegral_real_sinc_atTop.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
  have h2 : Tendsto (fun x : ℝ => Real.sin x * sinc x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sin_mul_sinc, Real.norm_eq_abs, abs_div, abs_of_pos hx, abs_of_nonneg (sq_nonneg _),
      div_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
    exact sin_sq_le_one x
  have h := h1.sub h2
  rw [sub_zero] at h
  exact h

/-- `sinc (b t)²` on `(0, ∞)`, antiderivative `Gs (b t)/b`. -/
theorem sincSq_data {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t => sinc (b * t) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), sinc (b * t) ^ 2 = π / 2 / b := by
  have hcont : ContinuousWithinAt (fun t => Gs (b * t) / b) (Ici 0) 0 :=
    ((continuous_Gs.comp (continuous_const.mul continuous_id :
      Continuous fun t : ℝ => b * t)).div_const b).continuousAt
      |>.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Gs (b * t) / b) (sinc (b * t) ^ 2) t := by
    intro t ht
    have h0 : HasDerivAt (fun y : ℝ => b * y) b t := by
      simpa using (hasDerivAt_id t).const_mul b
    have h := ((hasDerivAt_Gs (mul_pos hb ht)).comp t h0).div_const b
    refine h.congr_deriv ?_
    rw [mul_div_assoc, div_self hb.ne', mul_one]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ sinc (b * t) ^ 2 := fun t _ => sq_nonneg _
  have hlim : Tendsto (fun t => Gs (b * t) / b) atTop (𝓝 (π / 2 / b)) :=
    (tendsto_Gs.comp (Tendsto.const_mul_atTop hb tendsto_id)).div_const b
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  simp [Gs_zero]

/-- `1/(σ² + t²)` on `(0, ∞)`, antiderivative `arctan (t/σ)/σ`. -/
theorem lorentz_data {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => 1 / (σ ^ 2 + t ^ 2)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 1 / (σ ^ 2 + t ^ 2) = π / 2 / σ := by
  have hcont : ContinuousWithinAt (fun t => arctan (t / σ) / σ) (Ici 0) 0 :=
    ((continuous_arctan.comp (continuous_id.div_const σ)).div_const σ).continuousAt
      |>.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t => arctan (t / σ) / σ) (1 / (σ ^ 2 + t ^ 2)) t := by
    intro t _
    have h0 : HasDerivAt (fun y : ℝ => y / σ) (1 / σ) t := by
      simpa using (hasDerivAt_id t).div_const σ
    have h := ((hasDerivAt_arctan (t / σ)).comp t h0).div_const σ
    refine h.congr_deriv ?_
    have hσ' : σ ≠ 0 := hσ.ne'
    have h1 : 0 < 1 + (t / σ) ^ 2 := by positivity
    have h2 : 0 < σ ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hσ 2) (sq_nonneg t)
    field_simp
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (σ ^ 2 + t ^ 2) := fun t _ => by positivity
  have hlim : Tendsto (fun t => arctan (t / σ) / σ) atTop (𝓝 (π / 2 / σ)) :=
    ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
      (Tendsto.atTop_div_const hσ tendsto_id)).div_const σ
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  simp

/-- A function below `E/(σ² + t²) + C sinc(bt)²` on `(0, ∞)` has integral at most
`E π/(2σ) + C π/(2b)`. -/
theorem lintegral_le_of_bound {σ b E C : ℝ} (hσ : 0 < σ) (hb : 0 < b) (hE : 0 ≤ E)
    (hC : 0 ≤ C) {k : ℝ → ℝ}
    (hk : ∀ t ∈ Ioi (0 : ℝ), k t ≤ E * (1 / (σ ^ 2 + t ^ 2)) + C * sinc (b * t) ^ 2) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (k t) ≤
      ENNReal.ofReal (E * (π / 2 / σ) + C * (π / 2 / b)) := by
  obtain ⟨hA, hAi⟩ := lorentz_data hσ
  obtain ⟨hB, hBi⟩ := sincSq_data hb
  have hA' : Integrable (fun t : ℝ => E * (1 / (σ ^ 2 + t ^ 2))) (volume.restrict (Ioi 0)) :=
    Integrable.const_mul hA E
  have hB' : Integrable (fun t : ℝ => C * sinc (b * t) ^ 2) (volume.restrict (Ioi 0)) :=
    Integrable.const_mul hB C
  have hsum := hA'.add hB'
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (k t)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (E * (1 / (σ ^ 2 + t ^ 2)) + C * sinc (b * t) ^ 2) :=
        setLIntegral_mono_ae hsum.aemeasurable.ennreal_ofReal
          (ae_of_all _ fun t ht => ENNReal.ofReal_le_ofReal (hk t ht))
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (E * (1 / (σ ^ 2 + t ^ 2)) + C * sinc (b * t) ^ 2)) :=
        (ofReal_integral_eq_lintegral_ofReal hsum (ae_of_all _ fun t =>
          add_nonneg (mul_nonneg hE (by positivity)) (mul_nonneg hC (sq_nonneg _)))).symm
    _ = ENNReal.ofReal (E * (π / 2 / σ) + C * (π / 2 / b)) := by
        rw [integral_add hA' hB', integral_const_mul, integral_const_mul, hAi, hBi]

/-! ### The kernel, pointwise and integrated -/

/-- `|(e^{δs} - 1)/s|² ≤ (e^{δσ} - 1)²/(σ² + t²) + 4 e^{δσ} (δ/2)² sinc(δt/2)²`, `t > 0`,
`δ = log (1 + 1/T)`. -/
theorem kern_le {T σ t : ℝ} (hT : 0 < T) (hσ : 0 < σ) (ht : 0 < t) :
    kern T σ t ≤ (Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (1 / (σ ^ 2 + t ^ 2)) +
      4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
        sinc (Real.log (1 + 1 / T) / 2 * t) ^ 2 := by
  have hd0 : 0 < Real.log (1 + 1 / T) :=
    Real.log_pos (by have : 0 < 1 / T := one_div_pos.mpr hT; linarith)
  unfold kern
  generalize Real.log (1 + 1 / T) = d at hd0 ⊢
  have hd' : d ≠ 0 := hd0.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hy : d / 2 * t ≠ 0 := mul_ne_zero (div_ne_zero hd' two_ne_zero) ht'
  have hnum : ‖Complex.exp (↑d * (↑σ + ↑t * Complex.I)) - 1‖ ^ 2 =
      (Real.exp (d * σ) - 1) ^ 2 + 4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hz : (↑d * (↑σ + ↑t * Complex.I) : ℂ) = ↑(d * σ) + ↑(d * t) * Complex.I := by
      push_cast; ring
    rw [hz]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_re,
      Complex.exp_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add, sub_zero]
    have h2 : d * t = 2 * (d / 2 * t) := by ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (4 * Real.exp (d * σ) ^ 2 * Real.cos (d / 2 * t) ^ 2 -
      4 * Real.exp (d * σ)) * Real.sin_sq_add_cos_sq (d / 2 * t)
  rw [norm_div, div_pow, hnum, Complex.sq_norm, Complex.normSq_add_mul_I,
    sinc_of_ne_zero hy]
  have hden : 0 < σ ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hσ 2) (sq_nonneg t)
  have hcmp : 4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2 / (σ ^ 2 + t ^ 2) ≤
      4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2 / t ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos ht 2) (by nlinarith [sq_nonneg σ])
  have hid : 4 * Real.exp (d * σ) * (d / 2) ^ 2 * (Real.sin (d / 2 * t) / (d / 2 * t)) ^ 2 =
      4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2 / t ^ 2 := by
    field_simp <;> ring
  rw [hid]
  have hsplit : ((Real.exp (d * σ) - 1) ^ 2 + 4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2) /
      (σ ^ 2 + t ^ 2) = (Real.exp (d * σ) - 1) ^ 2 * (1 / (σ ^ 2 + t ^ 2)) +
      4 * Real.exp (d * σ) * Real.sin (d / 2 * t) ^ 2 / (σ ^ 2 + t ^ 2) := by
    rw [add_div, mul_one_div]
  rw [hsplit]
  linarith

/-- **The kernel integral, PROVED**: for `T > 0`, `σ > 0`, with `δ = log (1 + 1/T)`,
`∫_0^∞ |(e^{δs} - 1)/s|² dt ≤ (e^{δσ} - 1)² π/(2σ) + 4 e^{δσ} (δ/2)² π/(2 (δ/2))`. -/
theorem lintegral_kern_le {T σ : ℝ} (hT : 0 < T) (hσ : 0 < σ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t) ≤
      ENNReal.ofReal ((Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (π / 2 / σ) +
        4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
          (π / 2 / (Real.log (1 + 1 / T) / 2))) := by
  have hd0 : 0 < Real.log (1 + 1 / T) :=
    Real.log_pos (by have : 0 < 1 / T := one_div_pos.mpr hT; linarith)
  exact lintegral_le_of_bound hσ (half_pos hd0) (sq_nonneg _) (by positivity)
    (fun t ht => kern_le hT hσ ht)

/-! ### (22) from `K² ≤ 4` -/

/-- The numerical constant, a stronger form of the paper's `K² < 4.51`, p. 370:
`(Σ_p log p/(√p (p - 1)))² ≤ 4`. CITED numerical input; about 2.9635. -/
def Const4 : Prop := K451 ^ 2 ≤ 4

theorem const451_of_const4 (h : Const4) : Const451 := by
  unfold Const451; unfold Const4 at h; exact h.trans (by norm_num)

/-- the final real inequality for (22) -/
theorem final_alg {T σ d e : ℝ} (hT : 7.02 < T) (hσ1 : 1 / 2 < σ) (hσ2 : σ ≤ 3 / 4)
    (hd0 : 0 < d) (hd : d ≤ 1 / T) (he1 : 1 ≤ e) (he : e ≤ 1 + σ * (1 / T)) :
    4 * ((e - 1) ^ 2 * (π / 2 / σ) + 4 * e * (d / 2) ^ 2 * (π / 2 / (d / 2))) ≤
      4.51 * π / (T * (1 - σ / T)) := by
  have hT0 : 0 < T := by linarith
  have hσ0 : 0 < σ := by linarith
  have hπ := Real.pi_pos
  have hTne : T ≠ 0 := hT0.ne'
  have hσne : σ ≠ 0 := hσ0.ne'
  have hdne : d ≠ 0 := hd0.ne'
  have hB : 4 * e * (d / 2) ^ 2 * (π / 2 / (d / 2)) = π * (e * d) := by
    field_simp <;> ring
  have hA : (e - 1) ^ 2 * (π / 2 / σ) ≤ π * σ / (2 * T ^ 2) := by
    have h1 : (e - 1) ^ 2 ≤ (σ * (1 / T)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc (e - 1) ^ 2 * (π / 2 / σ) ≤ (σ * (1 / T)) ^ 2 * (π / 2 / σ) :=
          mul_le_mul_of_nonneg_right h1 (div_pos (by positivity) hσ0).le
      _ = π * σ / (2 * T ^ 2) := by field_simp <;> ring
  have hB2 : π * (e * d) ≤ π * ((1 + σ * (1 / T)) * (1 / T)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul he hd hd0.le
      (by have := mul_pos hσ0 (one_div_pos.mpr hT0); linarith)) hπ.le
  have hden : T * (1 - σ / T) = T - σ := by field_simp <;> ring
  have hTσ : 0 < T - σ := by linarith
  rw [hB, hden, le_div_iff₀ hTσ]
  have hsum : 4 * ((e - 1) ^ 2 * (π / 2 / σ) + π * (e * d)) * (T - σ) ≤
      4 * (π * σ / (2 * T ^ 2) + π * ((1 + σ * (1 / T)) * (1 / T))) * (T - σ) :=
    mul_le_mul_of_nonneg_right (by linarith) hTσ.le
  have heq : 4 * (π * σ / (2 * T ^ 2) + π * ((1 + σ * (1 / T)) * (1 / T))) * (T - σ) =
      π * (4 * (T + 3 / 2 * σ) * (T - σ)) / T ^ 2 := by
    field_simp <;> ring
  have hpoly : 4 * (T + 3 / 2 * σ) * (T - σ) ≤ 451 / 100 * T ^ 2 := by
    nlinarith [mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ T - 7.02),
      mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ 3 / 4 - σ), sq_nonneg σ]
  have hfin : π * (4 * (T + 3 / 2 * σ) * (T - σ)) / T ^ 2 ≤ 451 / 100 * π := by
    rw [div_le_iff₀ (pow_pos hT0 2)]
    nlinarith [mul_le_mul_of_nonneg_left hpoly hπ.le]
  have h451 : (4.51 : ℝ) = 451 / 100 := by norm_num
  rw [h451]
  linarith

/-- **(22), p. 370**, CONDITIONAL ON `Const4` only; the kernel integral is PROVED above. -/
theorem bound22_of_K4 (hC : Const4) : Bound22 := by
  intro T σ hT hσ1 hs
  have hT0 : 0 < T := by linarith
  have hσ0 : 0 < σ := by linarith
  have hkern0 : ∀ t, 0 ≤ kern T σ t := fun t => by unfold kern; positivity
  have hu : 0 < 1 / T := one_div_pos.mpr hT0
  have hd0 : 0 < Real.log (1 + 1 / T) := Real.log_pos (by linarith)
  have hd : Real.log (1 + 1 / T) ≤ 1 / T := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / T); linarith
  have he1 : 1 ≤ Real.exp (Real.log (1 + 1 / T) * σ) := Real.one_le_exp (mul_pos hd0 hσ0).le
  have he : Real.exp (Real.log (1 + 1 / T) * σ) ≤ 1 + σ * (1 / T) := by
    rw [← Real.rpow_def_of_pos (show (0 : ℝ) < 1 + 1 / T by linarith) σ]
    exact rpow_one_add_le_one_add_mul_self (by linarith) hσ0.le (by linarith)
  calc wInt T σ (primeC σ)
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (K451 ^ 2) * ENNReal.ofReal (kern T σ t) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h := norm_primeC_le hσ1.le t
        have : ‖primeC σ t‖ ^ 2 ≤ K451 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        nlinarith [hkern0 t]
    _ = ENNReal.ofReal (K451 ^ 2) * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t) :=
        lintegral_const_mul _ (measurable_kern T σ).ennreal_ofReal
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal
          ((Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (π / 2 / σ) +
            4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
              (π / 2 / (Real.log (1 + 1 / T) / 2))) := by
        gcongr
        · exact hC
        · exact lintegral_kern_le hT0 hσ0
    _ = ENNReal.ofReal (4 * ((Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (π / 2 / σ) +
            4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
              (π / 2 / (Real.log (1 + 1 / T) / 2)))) :=
        (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal (4.51 * π / (T * (1 - σ / T))) :=
        ENNReal.ofReal_le_ofReal (final_alg hT hσ1 hs hd0 hd he1 he)

/-- **Kaniecki 1995, Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920` under RH,
`Bound21` and `Const4`. -/
theorem lemma5_of_K4 (h4 : Lemma4) (hP : Parseval1920) (h21 : Bound21) (hC : Const4) :
    Lemma5 :=
  lemma5_of h4 hP h21 (bound22_of_K4 hC)

end LeanLab.Kaniecki1995.L5
