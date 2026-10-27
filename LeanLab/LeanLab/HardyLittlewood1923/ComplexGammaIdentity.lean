import LeanLab.HardyLittlewood1923.ComplexGammaLaplace

/-!
AI wrote this Lean code for CODEX task52.
The complex exponential Mellin identity serves P0004 page 8 equation 2.13.
-/

open Complex Real Set Filter MeasureTheory Metric

namespace LeanLab.HardyLittlewood1923.Task52

/-- The Gamma Laplace transform for a complex scale of positive real part. -/
theorem gammaLaplace_eq {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    gammaLaplace s z = z ^ (-s) * Complex.Gamma s := by
  have hReal : ∀ r : ℝ, 0 < r → gammaLaplace s (r : ℂ) =
      (r : ℂ) ^ (-s) * Complex.Gamma s := by
    intro r hr
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    simpa only [gammaLaplace, one_div, Complex.inv_cpow_ofReal_nonneg hr.le,
      Complex.cpow_neg, Complex.ofReal_neg, Complex.ofReal_mul, neg_mul] using h
  have hL : AnalyticOnNhd ℂ (gammaLaplace s) {w : ℂ | 0 < w.re} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (gammaLaplace_differentiable hs hw).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hR : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-s) * Complex.Gamma s)
      {w : ℂ | 0 < w.re} := by
    apply DifferentiableOn.analyticOnNhd _
      (isOpen_lt continuous_const Complex.continuous_re)
    intro w hw
    have hp : DifferentiableAt ℂ (fun u : ℂ => u ^ (-s)) w :=
      differentiableAt_id.cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
    exact (hp.mul_const _).differentiableWithinAt
  have hc : (1 : ℂ) ∈ closure
      ({w : ℂ | gammaLaplace s w = w ^ (-s) * Complex.Gamma s} \ {1}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d : ℝ := min (ε / 2) 1
    have hd : 0 < d := lt_min (by linarith) (by norm_num)
    refine ⟨((1 + d : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · exact hReal _ (by linarith)
      · simp only [mem_singleton_iff]
        intro h
        have h' := congr_arg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h'
        linarith
    · rw [dist_eq_norm]
      have he : ((1 + d : ℝ) : ℂ) - 1 = (d : ℂ) := by push_cast; ring
      rw [norm_sub_rev, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he := hL.eqOn_of_preconnected_of_mem_closure hR
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (1 : ℂ)) (by simp) hc
  exact he hz

/-- Complex inverse Mellin for the exponential weight. -/
theorem gamma_inverse_complex {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2)
    {z : ℂ} (hz : 0 < z.re) :
    (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))) =
        Complex.exp (-z) := by
  let f : ℝ → ℂ := fun t => Complex.exp (-z * t)
  have heq : ∀ s : ℂ, 0 < s.re → mellin f s =
      Complex.Gamma s * z ^ (-s) := by
    intro s hs
    simpa only [gammaLaplace, mellin, f, smul_eq_mul, mul_comm] using gammaLaplace_eq hs hz
  have hc : MellinConvergent f (σ : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul] using
      gammaLaplace_integrable (s := (σ : ℂ))
        (by simpa using (show (0 : ℝ) < σ by linarith)) hz
  have hv : Complex.VerticalIntegrable (mellin f) σ := by
    unfold Complex.VerticalIntegrable
    have he : (fun t : ℝ => mellin f ((σ : ℂ) + t * I)) =
        (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))) := by
      funext t
      exact heq _ (by simpa using (show (0 : ℝ) < σ by linarith))
    rw [he]
    exact gamma_kernel_integrable h1 h2 hz
  have h := mellinInv_mellin_eq σ f (x := 1) (by norm_num) hc hv (by dsimp [f]; fun_prop)
  unfold mellinInv at h
  simp only [Complex.ofReal_one, one_cpow, one_smul] at h
  have he : (∫ t : ℝ, mellin f ((σ : ℂ) + t * I)) =
      ∫ t : ℝ, Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I)) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => heq _ (by simpa using (show (0 : ℝ) < σ by linarith)))
  rw [he] at h
  simpa [f, Complex.real_smul] using h

#print axioms gammaLaplace_eq
#print axioms gamma_inverse_complex

end LeanLab.HardyLittlewood1923.Task52
