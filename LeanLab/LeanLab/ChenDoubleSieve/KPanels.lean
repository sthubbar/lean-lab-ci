import LeanLab.ChenDoubleSieve.LogIntegralPanels

/-!
# Exact weight moments and panels for the K integrals

Source: https://arxiv.org/pdf/0705.1652, pages 22 and 26, the K terms in Psi.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Panels

/-- The reciprocal of one minus t and its first panel moment. -/
theorem reflected_moments {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, (1 : ℝ) / (1 - t)) = log ((1 - a) / (1 - b)) ∧
    (∫ t in a..b, (t - a) * (1 / (1 - t))) =
      -(b - a) + (1 - a) * log ((1 - a) / (1 - b)) := by
  have hW : (∫ t in a..b, (1 : ℝ) / (1 - t)) = log ((1 - a) / (1 - b)) := by
    simp only [one_div]
    rw [integral_comp_sub_left (fun x : ℝ => x⁻¹), integral_inv_of_pos (by linarith) (by linarith)]
  have hw : ContinuousOn (fun t : ℝ => 1 / (1 - t)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.2]
  refine ⟨hW, ?_⟩
  have he : (∫ t in a..b, (t - a) * (1 / (1 - t))) =
      ∫ t in a..b, ((1 - a) * (1 / (1 - t)) - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 : 1 - t ≠ 0 := by rw [uIcc_of_le hab] at ht; linarith [ht.2]
    field_simp
    ring
  rw [he, integral_sub (hw.intervalIntegrable.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hW]
  simp
  ring

/-- Continuity of the K weight inside zero to one. -/
theorem K_weight_continuous {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ContinuousOn (fun t : ℝ => 1 / (t * (1 - t))) (Icc a b) := by
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  exact ne_of_gt (mul_pos (ha.trans_le ht.1) (by linarith [ht.2]))

/-- Exact zeroth and first moments of the K weight. -/
theorem K_moments {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, (1 : ℝ) / (t * (1 - t))) = log (b / a) + log ((1 - a) / (1 - b)) ∧
    (∫ t in a..b, (t - a) * (1 / (t * (1 - t)))) =
      log ((1 - a) / (1 - b)) - a * (log (b / a) + log ((1 - a) / (1 - b))) := by
  have hW1 := reciprocal_moments ha hab
  have hW2 := reflected_moments hab hb
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; change t ≠ 0; exact (ha.trans_le ht.1).ne'
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (1 - t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.2]
  have he (t : ℝ) (ht : t ∈ uIcc a b) :
      1 / (t * (1 - t)) = (1 : ℝ) / t + 1 / (1 - t) := by
    rw [uIcc_of_le hab] at ht
    have ht0 := (ha.trans_le ht.1).ne'
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
    field_simp
    ring
  constructor
  · have heq : (∫ t in a..b, (1 : ℝ) / (t * (1 - t))) =
        ∫ t in a..b, ((1 : ℝ) / t + 1 / (1 - t)) := integral_congr he
    rw [heq, integral_add hi1 hi2, hW1.1, hW2.1]
  · have heq : (∫ t in a..b, (t - a) * (1 / (t * (1 - t)))) =
        ∫ t in a..b, ((t - a) * (1 / t) + (t - a) * (1 / (1 - t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [he t ht]
      ring
    have hc : ContinuousOn (fun t : ℝ => t - a) (uIcc a b) := by fun_prop
    rw [heq, integral_add (hi1.continuousOn_mul hc) (hi2.continuousOn_mul hc), hW1.2, hW2.2]
    ring

/-- The logarithmic K integrand is integrable on each admissible panel. -/
theorem K_integrable {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : 0 < r) (hra : 0 < r * a - 1) :
    IntervalIntegrable (fun t => log (r * t - 1) / (t * (1 - t))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro t ht; have := ht.1; exact ne_of_gt (by nlinarith : 0 < r * t - 1)
  · fun_prop
  · intro t ht; exact ne_of_gt (mul_pos (ha.trans_le ht.1) (by linarith [ht.2]))

/-- The exact K panel lies between its weighted linear logarithm enclosures. -/
theorem K_panel {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : 0 < r) (hra : 0 < r * a - 1) :
    let W := log (b / a) + log ((1 - a) / (1 - b))
    let V := log ((1 - a) / (1 - b)) - a * W
    log (r * a - 1) * W + r / (r * b - 1) * V ≤
      (∫ t in a..b, log (r * t - 1) / (t * (1 - t))) ∧
    (∫ t in a..b, log (r * t - 1) / (t * (1 - t))) ≤
      log (r * a - 1) * W + r / (r * a - 1) * V := by
  have hm := K_moments ha hab hb
  have hfi : IntervalIntegrable (fun t => log (r * t - 1) * (1 / (t * (1 - t)))) volume a b := by
    simpa only [mul_one_div] using K_integrable ha hab hb hr hra
  have hp := weighted_linear_bounds hab (K_weight_continuous ha hab hb)
    (fun t ht => div_nonneg (by norm_num) (mul_nonneg (ha.trans_le ht.1).le (by linarith [ht.2])))
    hfi hm.1 hm.2
    (fun t ht => (log_affine_slopes hr hab hra ht).1)
    (fun t ht => (log_affine_slopes hr hab hra ht).2)
  simpa only [mul_one_div] using hp

end LeanLab.ChenDoubleSieve.Wu04Panels

#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.reflected_moments
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_weight_continuous
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_moments
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_integrable
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_panel
