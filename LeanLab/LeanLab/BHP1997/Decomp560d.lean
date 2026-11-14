/-
The strip Poisson kernel in Rademacher page 193 display 2.51.
This is supporting work for the harmonic multiplier, not a completed boundary construction.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Decomp560d
open Real Set MeasureTheory Filter
open scoped Topology

/-- Rademacher page 193 display 2.51, the normalized strip Poisson kernel. -/
noncomputable def stripPoissonKernel (σ t : ℝ) : ℝ :=
  Real.sin (Real.pi * σ) / (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * σ)))

/-- The interior horizontal parameter gives strictly positive sine and cosine gap.
Auxiliary estimate for Rademacher page 193 display 2.51. -/
theorem kernel_parameter_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < Real.sin (Real.pi * σ) ∧ 0 < 1 - |Real.cos (Real.pi * σ)| := by
  have hs : 0 < Real.sin (Real.pi * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hσ0) (by nlinarith [Real.pi_pos])
  refine ⟨hs, ?_⟩
  have hsq := Real.sin_sq_add_cos_sq (Real.pi * σ)
  have hab : |Real.cos (Real.pi * σ)| < 1 := by
    have hh := Real.abs_cos_le_one (Real.pi * σ)
    apply lt_of_le_of_ne hh
    intro he
    have hc : Real.cos (Real.pi * σ) ^ 2 = 1 := by
      calc
        _ = |Real.cos (Real.pi * σ)| ^ 2 := (sq_abs _).symm
        _ = 1 := by rw [he]; norm_num
    nlinarith [sq_pos_of_pos hs]
  linarith

/-- The strip Poisson denominator stays positive at every height.
Source Rademacher page 193 display 2.51. -/
theorem kernel_denominator_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    0 < 2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * σ)) := by
  have hc := (kernel_parameter_pos hσ0 hσ1).2
  have hh := Real.one_le_cosh (Real.pi * t)
  have ha := le_abs_self (Real.cos (Real.pi * σ))
  linarith

/-- Rademacher page 193 display 2.51, the strip Poisson kernel is positive in the interior. -/
theorem stripPoissonKernel_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    0 < stripPoissonKernel σ t := by
  exact div_pos (kernel_parameter_pos hσ0 hσ1).1 (kernel_denominator_pos hσ0 hσ1 t)

/-- Rademacher page 193 display 2.51, the strip kernel is even in height. -/
theorem stripPoissonKernel_even (σ t : ℝ) : stripPoissonKernel σ (-t) = stripPoissonKernel σ t := by
  simp [stripPoissonKernel, Real.cosh_neg]

/-- Rademacher page 193 displays 2.51 and 2.52, the kernel is continuous at every height. -/
theorem stripPoissonKernel_continuous {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (stripPoissonKernel σ) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  exact (kernel_denominator_pos hσ0 hσ1 t).ne'

/-- Exponential decay of the strip kernel, with an explicit constant depending on the horizontal parameter.
Auxiliary bound for Rademacher page 193 displays 2.51 and 2.52. -/
theorem stripPoissonKernel_exp_bound {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    ‖stripPoissonKernel σ t‖ ≤
      (Real.sin (Real.pi * σ) / (1 - |Real.cos (Real.pi * σ)|)) * Real.exp (-Real.pi * |t|) := by
  have hp := kernel_parameter_pos hσ0 hσ1
  have hc := Real.one_le_cosh (Real.pi * t)
  have he : Real.exp (Real.pi * |t|) ≤ 2 * Real.cosh (Real.pi * t) := by
    have ha : |Real.pi * t| = Real.pi * |t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [← Real.cosh_abs (Real.pi * t), ha, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * |t|))]
  have hcos : Real.cos (Real.pi * σ) ≤
      |Real.cos (Real.pi * σ)| * Real.cosh (Real.pi * t) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hc)
  have hden : (1 - |Real.cos (Real.pi * σ)|) * Real.exp (Real.pi * |t|) ≤
      2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * σ)) := by
    have hh := mul_le_mul_of_nonneg_left he hp.2.le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (stripPoissonKernel_pos hσ0 hσ1 t), stripPoissonKernel]
  calc
    _ ≤ Real.sin (Real.pi * σ) /
        ((1 - |Real.cos (Real.pi * σ)|) * Real.exp (Real.pi * |t|)) :=
      div_le_div_of_nonneg_left hp.1.le (mul_pos hp.2 (Real.exp_pos _)) hden
    _ = _ := by
      simp only [Real.exp_neg, neg_mul, div_eq_mul_inv, mul_inv]
      ring

/-- Two one-sided exponential integrals give integrability of exponential absolute-height decay.
Auxiliary estimate for Rademacher page 193 displays 2.51 to 2.53. -/
theorem exp_abs_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) := by
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    change Real.exp (-a * t) = Real.exp (-a * |t|)
    rw [abs_of_pos (show 0 < t from ht)]
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Iic (0 : ℝ)) := by
    apply (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun _ measurableSet_Iic
    intro t ht
    change Real.exp (a * t) = Real.exp (-a * |t|)
    rw [abs_of_nonpos (show t ≤ 0 from ht)]
    congr 1
    ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using hneg.union hpos

/-- Rademacher page 193 displays 2.51 to 2.53, the strip Poisson kernel is integrable in height. -/
theorem stripPoissonKernel_integrable {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Integrable (stripPoissonKernel σ) := by
  exact ((exp_abs_integrable Real.pi_pos).const_mul
      (Real.sin (Real.pi * σ) / (1 - |Real.cos (Real.pi * σ)|))).mono'
    (stripPoissonKernel_continuous hσ0 hσ1).aestronglyMeasurable
    (Filter.Eventually.of_forall (stripPoissonKernel_exp_bound hσ0 hσ1))

/-- Rademacher page 193 display 2.51, the strip kernel is smooth in height at each interior parameter. -/
theorem stripPoissonKernel_contDiff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContDiff ℝ ⊤ (stripPoissonKernel σ) := by
  apply ContDiff.div contDiff_const (by fun_prop)
  intro t
  exact (kernel_denominator_pos hσ0 hσ1 t).ne'

/-- An explicit arctangent primitive of the strip Poisson kernel.
Auxiliary normalization calculation for Rademacher page 193 display 2.51. -/
theorem stripPoissonKernel_has_primitive {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arctan
      ((Real.exp (Real.pi * u) - Real.cos (Real.pi * σ)) / Real.sin (Real.pi * σ)) / Real.pi)
      (stripPoissonKernel σ t) t := by
  have hs := (kernel_parameter_pos hσ0 hσ1).1
  have hh := ((((Real.hasDerivAt_exp (Real.pi * t)).comp t
    ((hasDerivAt_id t).const_mul Real.pi)).sub_const (Real.cos (Real.pi * σ))).div_const
      (Real.sin (Real.pi * σ))).arctan.div_const Real.pi
  convert hh using 1 <;> simp only [stripPoissonKernel, Function.comp_def, mul_one]
  rw [Real.cosh_eq, Real.exp_neg]
  have hsq := Real.sin_sq_add_cos_sq (Real.pi * σ)
  field_simp [hs.ne', Real.pi_ne_zero, Real.exp_ne_zero]
  have heq : Real.sin (Real.pi * σ) ^ 2 + (Real.exp (Real.pi * t) - Real.cos (Real.pi * σ)) ^ 2 =
      Real.exp (Real.pi * t) ^ 2 + 1 - 2 * Real.exp (Real.pi * t) * Real.cos (Real.pi * σ) := by
    nlinarith [hsq]
  rw [← heq, div_self]
  nlinarith [sq_pos_of_pos hs, sq_nonneg (Real.exp (Real.pi * t) - Real.cos (Real.pi * σ))]

/-- Rademacher page 193 displays 2.51 to 2.53, the left boundary kernel has mass one minus sigma. -/
theorem stripPoissonKernel_mass {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∫ t : ℝ, stripPoissonKernel σ t) = 1 - σ := by
  have hs := (kernel_parameter_pos hσ0 hσ1).1
  let F : ℝ → ℝ := fun t => Real.arctan
    ((Real.exp (Real.pi * t) - Real.cos (Real.pi * σ)) / Real.sin (Real.pi * σ)) / Real.pi
  have harctan : Real.arctan (-Real.cos (Real.pi * σ) / Real.sin (Real.pi * σ)) =
      Real.pi * σ - Real.pi / 2 := by
    have he : -Real.cos (Real.pi * σ) / Real.sin (Real.pi * σ) =
        Real.tan (Real.pi * σ - Real.pi / 2) := by
      rw [show Real.pi * σ - Real.pi / 2 = -(Real.pi / 2 - Real.pi * σ) by ring,
        Real.tan_neg, Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
      ring
    rw [he, Real.arctan_tan (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  have hbot : Tendsto F atBot (𝓝 (σ - 1 / 2)) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot Real.pi_pos)
    have harg := (hexp.sub_const (Real.cos (Real.pi * σ))).div_const (Real.sin (Real.pi * σ))
    have hh := ((Real.continuous_arctan.tendsto _).comp harg).div_const Real.pi
    convert hh using 1 <;> simp only [F, Function.comp_def, zero_sub, harctan]
    field_simp [Real.pi_ne_zero]
  have htop : Tendsto F atTop (𝓝 (1 / 2 : ℝ)) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
    have harg : Tendsto (fun t : ℝ =>
        (Real.exp (Real.pi * t) - Real.cos (Real.pi * σ)) / Real.sin (Real.pi * σ)) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        (hexp.atTop_add (tendsto_const_nhds (x := -Real.cos (Real.pi * σ)))).atTop_div_const hs
    have hh := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg).div_const Real.pi
    convert hh using 1 <;> try dsimp only [F, Function.comp_def]
    field_simp [Real.pi_ne_zero]
  have hh := integral_of_hasDerivAt_of_tendsto
    (fun t => stripPoissonKernel_has_primitive hσ0 hσ1 t)
    (stripPoissonKernel_integrable hσ0 hσ1) hbot htop
  linarith

/-- Rademacher page 193 display 2.6, the logarithmic left boundary with exponent minus one. -/
noncomputable def logBoundary (c y : ℝ) : ℝ :=
  -Real.log ‖(c : ℂ) + (y : ℂ) * Complex.I‖

/-- The logarithmic boundary data in display 2.6 are continuous when their real offset is positive. -/
theorem logBoundary_continuous {c : ℝ} (hc : 0 < c) : Continuous (logBoundary c) := by
  have hn : Continuous (fun y : ℝ => ‖(c : ℂ) + (y : ℂ) * Complex.I‖) := by fun_prop
  apply (hn.log ?_).neg
  intro y
  have hh := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at hh
  rw [abs_of_pos hc] at hh
  exact ne_of_gt (hc.trans_le hh)

/-- Linear height bounds for the logarithmic boundary data in Rademacher page 193 display 2.6. -/
theorem logBoundary_norm_bound {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖logBoundary c y‖ ≤ (|Real.log c| + c + 1) + |y| := by
  have hl := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * Complex.I)
  have hu := Complex.norm_le_abs_re_add_abs_im ((c : ℂ) + (y : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_add] at hl hu
  rw [abs_of_pos hc] at hl hu
  have hnp : 0 < ‖(c : ℂ) + (y : ℂ) * Complex.I‖ := hc.trans_le hl
  have hlo := Real.log_le_log hc hl
  have hhi := Real.log_le_sub_one_of_pos hnp
  simp only [logBoundary, norm_neg, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log c), neg_abs_le (Real.log c), abs_nonneg y]

/-- The linear logarithmic majorant satisfies the exponential integrability condition of display 2.53. -/
theorem exp_abs_linear_integrable {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun y : ℝ => (C + |y|) * Real.exp (-Real.pi * |y|)) := by
  apply (((exp_abs_integrable (by positivity : 0 < Real.pi / 2)).const_mul (C + 1))).mono'
    (by fun_prop)
  filter_upwards with y
  have h1 : 1 ≤ Real.exp ((Real.pi / 2) * |y|) := Real.one_le_exp (by positivity)
  have hy : |y| ≤ Real.exp ((Real.pi / 2) * |y|) := by
    have hh := Real.add_one_le_exp ((Real.pi / 2) * |y|)
    nlinarith [mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi / 2 - 1) (abs_nonneg y)]
  have hh : C + |y| ≤ (C + 1) * Real.exp ((Real.pi / 2) * |y|) := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr h1)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((C + 1) * Real.exp ((Real.pi / 2) * |y|)) * Real.exp (-Real.pi * |y|) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The actual logarithmic boundary convolution in Rademacher page 193 display 2.52 converges absolutely. -/
theorem logBoundary_convolution_integrable {c σ : ℝ} (hc : 0 < c) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (t : ℝ) : Integrable (fun y : ℝ => stripPoissonKernel σ (t - y) * logBoundary c y) := by
  let C : ℝ := |Real.log c| + c + 1
  let D : ℝ := Real.sin (Real.pi * σ) / (1 - |Real.cos (Real.pi * σ)|)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 < D := div_pos (kernel_parameter_pos hσ0 hσ1).1 (kernel_parameter_pos hσ0 hσ1).2
  have hcont : Continuous (fun y : ℝ => stripPoissonKernel σ (t - y) * logBoundary c y) :=
    ((stripPoissonKernel_continuous hσ0 hσ1).comp (continuous_const.sub continuous_id)).mul
      (logBoundary_continuous hc)
  apply ((exp_abs_linear_integrable hC).const_mul (D * Real.exp (Real.pi * |t|))).mono'
    hcont.aestronglyMeasurable
  filter_upwards with y
  have hheight : |y| ≤ |t - y| + |t| := by
    calc
      _ = |(y - t) + t| := by congr 1; ring
      _ ≤ |y - t| + |t| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  have he : Real.exp (-Real.pi * |t - y|) ≤ Real.exp (Real.pi * |t|) * Real.exp (-Real.pi * |y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hheight)]
  have hk : ‖stripPoissonKernel σ (t - y)‖ ≤
      D * (Real.exp (Real.pi * |t|) * Real.exp (-Real.pi * |y|)) :=
    (stripPoissonKernel_exp_bound hσ0 hσ1 (t - y)).trans (mul_le_mul_of_nonneg_left he hD.le)
  rw [norm_mul]
  calc
    _ ≤ (D * (Real.exp (Real.pi * |t|) * Real.exp (-Real.pi * |y|))) * (C + |y|) :=
      mul_le_mul hk (logBoundary_norm_bound hc y) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Rademacher page 193 display 2.52, the real Poisson integral for the logarithmic left boundary and zero right boundary. -/
noncomputable def stripLogPotential (c σ t : ℝ) : ℝ :=
  ∫ y : ℝ, stripPoissonKernel σ (t - y) * logBoundary c y

/-- Rademacher page 193 display 2.6, the logarithmic boundary data are even in height. -/
theorem logBoundary_even (c y : ℝ) : logBoundary c (-y) = logBoundary c y := by
  have he : (c : ℂ) + ((-y : ℝ) : ℂ) * Complex.I =
      (starRingEnd ℂ) ((c : ℂ) + (y : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  simp only [logBoundary]
  rw [he, Complex.norm_conj]

/-- Rademacher page 194 before display 2.8, the actual Poisson integral is symmetric in height. -/
theorem stripLogPotential_even (c σ t : ℝ) : stripLogPotential c σ (-t) = stripLogPotential c σ t := by
  unfold stripLogPotential
  calc
    _ = ∫ y : ℝ, stripPoissonKernel σ (-t - (-y)) * logBoundary c (-y) :=
      (integral_neg_eq_self (fun y : ℝ => stripPoissonKernel σ (-t - y) * logBoundary c y) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show -t - (-y) = -(t - y) by ring, stripPoissonKernel_even, logBoundary_even]

end LeanLab.BHP1997.Decomp560d
