import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# Weighted linear panels for Wu's logarithmic integrals

Source: https://arxiv.org/pdf/0705.1652, pages 22 and 26, the scalar terms in Psi1 and Psi2.
These panel bounds retain first derivative variation and avoid floating point quadrature.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Panels

/-- Endpoint derivative bounds give linear enclosures for log of an affine function. -/
theorem log_affine_slopes {a b r t : ℝ} (hr : 0 < r) (hab : a ≤ b)
    (ha : 0 < r * a - 1) (ht : t ∈ Icc a b) :
    log (r * a - 1) + r / (r * b - 1) * (t - a) ≤ log (r * t - 1) ∧
    log (r * t - 1) ≤ log (r * a - 1) + r / (r * a - 1) * (t - a) := by
  have hta : 0 < r * t - 1 := by nlinarith [ht.1]
  have hba : 0 < r * b - 1 := by nlinarith
  have hl := one_sub_inv_le_log_of_pos (div_pos hta ha)
  have hu := log_le_sub_one_of_pos (div_pos hta ha)
  rw [log_div hta.ne' ha.ne'] at hl hu
  have el : 1 - ((r * t - 1) / (r * a - 1))⁻¹ = r * (t - a) / (r * t - 1) := by
    field_simp
    <;> ring
  have eu : (r * t - 1) / (r * a - 1) - 1 = r / (r * a - 1) * (t - a) := by
    field_simp
    <;> ring
  rw [el] at hl
  rw [eu] at hu
  have hd : r * (t - a) / (r * b - 1) ≤ r * (t - a) / (r * t - 1) :=
    div_le_div_of_nonneg_left (mul_nonneg hr.le (sub_nonneg.mpr ht.1)) hta (by nlinarith [ht.2])
  constructor
  · have he : r / (r * b - 1) * (t - a) = r * (t - a) / (r * b - 1) := by ring
    rw [he]
    linarith
  · linarith

/-- Integrate any pair of linear enclosures against a nonnegative continuous weight. -/
theorem weighted_linear_bounds {f w : ℝ → ℝ} {a b L U l u W V : ℝ} (hab : a ≤ b)
    (hwi : ContinuousOn w (Icc a b)) (hw : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hfi : IntervalIntegrable (fun t => f t * w t) volume a b)
    (hW : (∫ t in a..b, w t) = W) (hV : (∫ t in a..b, (t - a) * w t) = V)
    (hlo : ∀ t ∈ Icc a b, L + l * (t - a) ≤ f t)
    (hhi : ∀ t ∈ Icc a b, f t ≤ U + u * (t - a)) :
    L * W + l * V ≤ (∫ t in a..b, f t * w t) ∧
    (∫ t in a..b, f t * w t) ≤ U * W + u * V := by
  have hwi' : ContinuousOn w (uIcc a b) := by rwa [uIcc_of_le hab]
  have hi : IntervalIntegrable w volume a b := hwi'.intervalIntegrable
  have hti : IntervalIntegrable (fun t => (t - a) * w t) volume a b :=
    ((continuous_id.sub continuous_const).continuousOn.mul hwi').intervalIntegrable
  have he (A B : ℝ) : (∫ t in a..b, (A + B * (t - a)) * w t) = A * W + B * V := by
    have hf : (fun t => (A + B * (t - a)) * w t) = fun t => A * w t + B * ((t - a) * w t) := by
      funext t; ring
    rw [hf, integral_add (hi.const_mul A) (hti.const_mul B),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hW, hV]
  have hei (A B : ℝ) : IntervalIntegrable (fun t => (A + B * (t - a)) * w t) volume a b := by
    have hf : (fun t => (A + B * (t - a)) * w t) = fun t => A * w t + B * ((t - a) * w t) := by
      funext t; ring
    rw [hf]
    exact (hi.const_mul A).add (hti.const_mul B)
  constructor
  · rw [← he L l]
    exact integral_mono_on hab (hei L l) hfi (fun t ht => mul_le_mul_of_nonneg_right (hlo t ht) (hw t ht))
  · rw [← he U u]
    exact integral_mono_on hab hfi (hei U u) (fun t ht => mul_le_mul_of_nonneg_right (hhi t ht) (hw t ht))

/-- Exact moments of the reciprocal weight used in J. -/
theorem reciprocal_moments {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 : ℝ) / t) = log (b / a) ∧
    (∫ t in a..b, (t - a) * (1 / t)) = (b - a) - a * log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hw : ContinuousOn (fun t : ℝ => 1 / t) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; exact (ha.trans_le ht.1).ne'
  have hW : (∫ t in a..b, (1 : ℝ) / t) = log (b / a) := by
    simpa only [one_div, log_div hb.ne' ha.ne'] using integral_inv_of_pos ha hb
  refine ⟨hW, ?_⟩
  have he : (∫ t in a..b, (t - a) * (1 / t)) = ∫ t in a..b, (1 - a * (1 / t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hab] at ht; exact (ha.trans_le ht.1).ne'
    field_simp
  rw [he, integral_sub intervalIntegrable_const (hw.intervalIntegrable.const_mul a),
    intervalIntegral.integral_const_mul, hW]
  simp

/-- A certified panel for the logarithmic J integral. -/
theorem J_panel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    log (a - 1) * log (b / a) + ((b - a) - a * log (b / a)) / (b - 1) ≤
      (∫ t in a..b, log (t - 1) / t) ∧
    (∫ t in a..b, log (t - 1) / t) ≤
      log (a - 1) * log (b / a) + ((b - a) - a * log (b / a)) / (a - 1) := by
  have hW := reciprocal_moments (show 0 < a by linarith) hab
  have hw : ContinuousOn (fun t : ℝ => 1 / t) (Icc a b) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; linarith [ht.1]
  have hfi : IntervalIntegrable (fun t => log (t - 1) * (1 / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.mul _ hw
    apply ContinuousOn.log (by fun_prop)
    intro t ht; linarith [ht.1]
  have hb := weighted_linear_bounds hab hw (fun t ht => div_nonneg (by norm_num) (by linarith [ht.1])) hfi hW.1 hW.2
    (fun t ht => by simpa only [one_mul, one_div] using
      (log_affine_slopes (r := 1) (by norm_num) hab (by linarith) ht).1)
    (fun t ht => by simpa only [one_mul, one_div] using
      (log_affine_slopes (r := 1) (by norm_num) hab (by linarith) ht).2)
  simpa only [mul_one_div, one_mul, inv_mul_eq_div] using hb

end LeanLab.ChenDoubleSieve.Wu04Panels

#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.log_affine_slopes
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.weighted_linear_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.reciprocal_moments
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.J_panel
