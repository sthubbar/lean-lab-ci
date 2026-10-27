import LeanLab.HardyLittlewood1923.WeightedSharp

/-!
AI wrote this Lean code for CODEX task52.
P0004 page 19, integration of the Gamma decay envelope.
-/

open Real Set MeasureTheory

namespace LeanLab.HardyLittlewood1923.Task52

lemma one_add_rpow_bound {p t : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (ht : 0 ≤ t) :
    (1 + t) ^ p ≤ 4 * (1 + t ^ p) := by
  by_cases ht1 : t ≤ 1
  · have h := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + t) (by linarith : 1 + t ≤ 2) hp
    have h2 : (2 : ℝ) ^ p ≤ 4 := by
      calc _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
        _ = _ := by norm_num
    nlinarith [Real.rpow_nonneg ht p]
  · have ht0 : 0 < t := by linarith
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + t) (by linarith : 1 + t ≤ 2 * t) hp
    rw [Real.mul_rpow (by norm_num) ht] at h
    have h2 : (2 : ℝ) ^ p ≤ 4 := by
      calc _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
        _ = _ := by norm_num
    nlinarith [Real.rpow_nonneg ht p, mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht p)]

lemma integrable_rpow_envelope {p δ : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ p * Real.exp (-(δ * |t|))) := by
  apply Integrable.mono' (integrable_polynomial_exp_abs 2 hδ)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (1 + |t|) ^ p * Real.exp (-(δ * |t|)))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg t] : 1 ≤ 1 + |t|) hp2
    simpa only [Real.rpow_ofNat, neg_mul] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(δ * |t|))).le

lemma integral_rpow_envelope_le {p δ : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hδ : 0 < δ) :
    (∫ t : ℝ, (1 + |t|) ^ p * Real.exp (-(δ * |t|))) ≤
      8 * (1 / δ + (1 / δ) ^ (p + 1) * Real.Gamma (p + 1)) := by
  rw [integral_comp_abs (f := fun t : ℝ => (1 + t) ^ p * Real.exp (-(δ * t)))]
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(δ * t))) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := δ)
      (by norm_num) (by norm_num) hδ
  have hm : IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(δ * t))) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p) (b := δ)
      (by linarith) (by norm_num) hδ
  have hf : IntegrableOn (fun t : ℝ => (1 + t) ^ p * Real.exp (-(δ * t))) (Ioi 0) :=
    (integrable_rpow_envelope hp hp2 hδ).integrableOn.congr_fun
      (fun t ht => by dsimp only; rw [abs_of_pos ht]) measurableSet_Ioi
  have hb : (∫ t : ℝ in Ioi 0, (1 + t) ^ p * Real.exp (-(δ * t))) ≤
      ∫ t : ℝ in Ioi 0, 4 * (Real.exp (-(δ * t)) + t ^ p * Real.exp (-(δ * t))) := by
    apply integral_mono_ae hf ((he.add hm).const_mul 4)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have h := mul_le_mul_of_nonneg_right (one_add_rpow_bound hp hp2 ht.le)
      (Real.exp_pos (-(δ * t))).le
    change (1 + t) ^ p * Real.exp (-(δ * t)) ≤
      4 * (Real.exp (-(δ * t)) + t ^ p * Real.exp (-(δ * t)))
    nlinarith only [h]
  rw [integral_const_mul, integral_add he hm] at hb
  have h0 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (by norm_num) hδ
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (by linarith) hδ
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at h0
  simp only [add_sub_cancel_right] at h1
  rw [h0, h1] at hb
  linarith only [hb]

#print axioms one_add_rpow_bound
#print axioms integrable_rpow_envelope
#print axioms integral_rpow_envelope_le

end LeanLab.HardyLittlewood1923.Task52
