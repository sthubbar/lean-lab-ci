import LeanLab.HardyLittlewood1923.ExponentialMellin

/-!
AI wrote this Lean code for CODEX task52.
These Laplace integral helpers serve the complex exponential Mellin identity on P0004 page 8.
-/

open Complex Real Set Filter MeasureTheory Metric

namespace LeanLab.HardyLittlewood1923.Task52

noncomputable def gammaLaplace (s z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)

lemma gammaLaplace_continuousOn (s z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.cpow_const
      (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht)
  · fun_prop

lemma gammaLaplace_integrable {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re - 1) (b := z.re) (by linarith) (by norm_num) hz
  refine Integrable.mono' hb ((gammaLaplace_continuousOn s z).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

lemma gammaLaplace_differentiable {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    DifferentiableAt ℂ (gammaLaplace s) z := by
  let F : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (s - 1) * (Complex.exp (-w * t) * (-t))
  let r : ℝ := z.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hm : ∀ w : ℂ, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) :=
    fun w => (gammaLaplace_continuousOn s w).aestronglyMeasurable measurableSet_Ioi
  have hm' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    dsimp [F']
    simp only [← mul_assoc]
    exact (gammaLaplace_continuousOn s z).mul
      (show ContinuousOn (fun t : ℝ => -(t : ℂ)) (Ioi 0) by fun_prop)
  have hb : IntegrableOn (fun t : ℝ => t ^ s.re * Real.exp (-r * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re) (b := r) (by linarith) (by norm_num) hr
  have hd : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      HasDerivAt (fun w => F w t) (F' w t) w := by
    apply Eventually.of_forall
    intro t w hw
    dsimp [F, F']
    simpa using (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).const_mul
      ((t : ℂ) ^ (s - 1))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      ‖F' w t‖ ≤ t ^ s.re * Real.exp (-r * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    intro w hw
    have hw' : r ≤ w.re := by
      have hn : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
      have hre := Complex.abs_re_le_norm (w - z)
      have hre' := (abs_le.mp (le_trans hre hn.le)).1
      simp only [sub_re] at hre'
      dsimp [r] at *
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    have he : (-w * (t : ℂ)).re = -w.re * t := by simp
    rw [he]
    have hp : t ^ (s.re - 1) * t = t ^ s.re := by
      conv_lhs => arg 2; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc _ = (t ^ (s.re - 1) * t) * Real.exp (-w.re * t) := by simp; ring
      _ = t ^ s.re * Real.exp (-w.re * t) := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hw') ht.le))
        (Real.rpow_nonneg ht.le _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := ball z r) (μ := volume.restrict (Ioi 0))
    (ball_mem_nhds z hr) (Eventually.of_forall hm)
    (gammaLaplace_integrable hs hz) hm' hbound hb hd
  exact h.2.differentiableAt

#print axioms gammaLaplace_continuousOn
#print axioms gammaLaplace_integrable
#print axioms gammaLaplace_differentiable

end LeanLab.HardyLittlewood1923.Task52
