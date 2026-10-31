/-
The L1 convolution identity in Helfgott, arXiv:1312.7748v2, display 7.20 on page 60.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.MellinSup

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.MellinL1
open EtaTwo EtaTwoMoments GaussianL2 MellinL2 MellinSup

/-- The Mellin kernel before squaring. -/
noncomputable def kernel (t w : ℝ) : ℝ := etaTwo t * phi (w / t) / t

/-- Integrability and exact mass of each positive parameter fiber. -/
theorem kernel_fiber (t : ℝ) (ht : 0 < t) :
    IntegrableOn (kernel t) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), kernel t w) = etaTwo t * Real.sqrt (Real.pi / 2) := by
  have hint : IntegrableOn (fun w : ℝ => phi (w / t)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_right_iff phi 0 (inv_pos.mpr ht)).mpr
      (by simpa using phi_integrable)
    simpa only [div_eq_mul_inv] using h
  have he : (∫ w in Ioi (0 : ℝ), phi (w / t)) = t * Real.sqrt (Real.pi / 2) := by
    have h := integral_comp_mul_right_Ioi phi 0 (inv_pos.mpr ht)
    simpa only [zero_mul, inv_inv, smul_eq_mul, phi_integral, div_eq_mul_inv] using h
  have hfun : kernel t = fun w : ℝ => (etaTwo t / t) * phi (w / t) := by
    funext w
    unfold kernel
    ring
  constructor
  · rw [hfun]
    exact hint.const_mul _
  · rw [hfun, integral_const_mul, he]
    field_simp

#print axioms kernel_fiber

/-- Product integrability for the L1 Fubini calculation. -/
theorem kernel_integrable : Integrable (Function.uncurry kernel)
    ((volume.restrict (Ioc (1 / 4 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have heta : Measurable etaTwo := by
    have h : Measurable (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0) := by
      fun_prop
    exact Measurable.ite measurableSet_Ioi h measurable_const
  have he (t : ℝ) : 0 ≤ etaTwo t := by
    unfold etaTwo
    split_ifs <;> positivity
  have hp : Continuous phi := by unfold phi; fun_prop
  have hm : Measurable (Function.uncurry kernel) :=
    ((heta.comp measurable_fst).mul
      (hp.measurable.comp (measurable_snd.div measurable_fst))).div measurable_fst
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * Real.sqrt (Real.pi / 2))
      (Icc (1 / 4 : ℝ) 1) := continuousOn_etaTwo.mul_const _
  have ho : IntegrableOn (fun t : ℝ => etaTwo t * Real.sqrt (Real.pi / 2))
      (Ioc (1 / 4 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (hc.intervalIntegrable_of_Icc (by norm_num))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact (kernel_fiber t (by linarith [ht.1])).1
  · apply ho.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hn (w : ℝ) : ‖kernel t w‖ = kernel t w := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      have hφ : 0 ≤ phi (w / t) := by unfold phi; positivity
      exact div_nonneg (mul_nonneg (he t) hφ) ht0.le
    simp only [Function.uncurry_apply_pair]
    simp_rw [hn]
    exact (kernel_fiber t ht0).2.symm

#print axioms kernel_integrable

/-- The unscaled smoothing is integrable and has exactly the Gaussian mass. -/
theorem mellin_integral : IntegrableOn mellin (Ioi (0 : ℝ)) ∧
    (∫ w in Ioi (0 : ℝ), mellin w) = Real.sqrt (Real.pi / 2) := by
  have hi := kernel_integrable.integral_prod_right
  have hs := intervalIntegral_integral_swap (a := (1 / 4 : ℝ)) (b := (1 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := kernel)
    (by simpa only [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] using kernel_integrable)
  have hmass : (∫ t in (1 / 4 : ℝ)..1, etaTwo t) = 1 := by
    have h := etaTwo_moment_compact 0
    norm_num at h
    exact h
  constructor
  · change Integrable (fun w : ℝ => ∫ t in (1 / 4 : ℝ)..1, kernel t w)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1),
      Function.uncurry_apply_pair] using hi
  · change (∫ w in Ioi (0 : ℝ), ∫ t in (1 / 4 : ℝ)..1, kernel t w) = _
    rw [← hs]
    calc
      _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t * Real.sqrt (Real.pi / 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        exact (kernel_fiber t (by linarith [ht.1])).2
      _ = _ := by rw [intervalIntegral.integral_mul_const, hmass, one_mul]

#print axioms mellin_integral

/-- Display 7.20 as an actual absolute integral for every positive scale. -/
theorem etaStar_abs_integral (k : ℝ) (hk : 0 < k) :
    IntegrableOn (etaStar k) (Ioi (0 : ℝ)) ∧
      (∫ w in Ioi (0 : ℝ), |etaStar k w|) = Real.sqrt (Real.pi / 2) / k := by
  have hi : IntegrableOn (fun w : ℝ => mellin (k * w)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff mellin 0 hk).mpr
      (by simpa only [mul_zero] using mellin_integral.1)
  have hs : (∫ w in Ioi (0 : ℝ), etaStar k w) =
      k⁻¹ * Real.sqrt (Real.pi / 2) := by
    simpa only [etaStar, mul_zero, smul_eq_mul, mellin_integral.2] using
      integral_comp_mul_left_Ioi mellin 0 hk
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ w in Ioi (0 : ℝ), etaStar k w := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      exact abs_of_nonneg (mellin_sup (k * w)).1
    _ = k⁻¹ * Real.sqrt (Real.pi / 2) := hs
    _ = Real.sqrt (Real.pi / 2) / k := by ring

#print axioms etaStar_abs_integral

end LeanLab.Helfgott2013.MellinL1
