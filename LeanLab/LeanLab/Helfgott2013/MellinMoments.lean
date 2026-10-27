/-
Actual Mellin moments behind Helfgott, arXiv:1312.7748v2, display 7.11 on page 58.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.SmoothingNorms
import LeanLab.Helfgott2013.GaussianMoments

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.MellinMoments
open EtaTwo EtaTwoMoments GaussianL2 GaussianMoments MellinL2 MellinSup

/-- The Mellin kernel with a nonnegative integer moment weight. -/
noncomputable def momentKernel (k : ℕ) (t w : ℝ) : ℝ :=
  etaTwo t * phi (w / t) / t * w ^ k

/-- The exact positive parameter fiber integral for every moment. -/
theorem moment_fiber (k : ℕ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (momentKernel k t) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), momentKernel k t w) =
        etaTwo t * t ^ k * ∫ u in Ioi (0 : ℝ), phi u * u ^ k := by
  have hint : IntegrableOn (fun w : ℝ => phi (w / t) * (w / t) ^ k) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_right_iff (fun u : ℝ => phi u * u ^ k)
      0 (inv_pos.mpr ht)).mpr (by simpa using phi_moment_integrable k)
    simpa only [div_eq_mul_inv] using h
  have he : (∫ w in Ioi (0 : ℝ), phi (w / t) * (w / t) ^ k) =
      t * ∫ u in Ioi (0 : ℝ), phi u * u ^ k := by
    have h := integral_comp_mul_right_Ioi (fun u : ℝ => phi u * u ^ k) 0 (inv_pos.mpr ht)
    simpa only [zero_mul, inv_inv, smul_eq_mul, div_eq_mul_inv] using h
  have hfun : momentKernel k t = fun w : ℝ =>
      (etaTwo t * t ^ k / t) * (phi (w / t) * (w / t) ^ k) := by
    funext w
    have hw : t ^ k * (w / t) ^ k = w ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp
    unfold momentKernel
    rw [← hw]
    ring
  constructor
  · rw [hfun]
    exact hint.const_mul _
  · rw [hfun, integral_const_mul, he]
    field_simp

#print axioms moment_fiber

/-- Product integrability for every natural Mellin moment. -/
theorem moment_integrable (k : ℕ) : Integrable (Function.uncurry (momentKernel k))
    ((volume.restrict (Ioc (1 / 4 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have heta : Measurable etaTwo := by
    have h : Measurable (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0) := by
      fun_prop
    exact Measurable.ite measurableSet_Ioi h measurable_const
  have hp : Continuous phi := by unfold phi; fun_prop
  have hm : Measurable (Function.uncurry (momentKernel k)) :=
    (((heta.comp measurable_fst).mul
      (hp.measurable.comp (measurable_snd.div measurable_fst))).div measurable_fst).mul
        (measurable_snd.pow_const k)
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * t ^ k *
      ∫ u in Ioi (0 : ℝ), phi u * u ^ k) (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.mul (continuousOn_id.pow k)).mul_const _
  have ho : IntegrableOn (fun t : ℝ => etaTwo t * t ^ k *
      ∫ u in Ioi (0 : ℝ), phi u * u ^ k) (Ioc (1 / 4 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (hc.intervalIntegrable_of_Icc (by norm_num))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact (moment_fiber k t (by linarith [ht.1])).1
  · apply ho.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hn : (∫ w in Ioi (0 : ℝ), ‖momentKernel k t w‖) =
        ∫ w in Ioi (0 : ℝ), momentKernel k t w := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w hw
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg]
      have he : 0 ≤ etaTwo t := by unfold etaTwo; split_ifs <;> positivity
      have hφ : 0 ≤ phi (w / t) := by unfold phi; positivity
      exact mul_nonneg (div_nonneg (mul_nonneg he hφ) ht0.le) (pow_nonneg hw.le k)
    simp only [Function.uncurry_apply_pair]
    rw [hn]
    exact (moment_fiber k t ht0).2.symm

#print axioms moment_integrable

/-- Fubini factors every natural moment of the actual Mellin smoothing. -/
theorem mellin_moment (k : ℕ) :
    IntegrableOn (fun w : ℝ => mellin w * w ^ k) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), mellin w * w ^ k) =
        (2 * (1 - (1 / 2 : ℝ) ^ (k + 1)) / (k + 1)) ^ 2 *
          ∫ u in Ioi (0 : ℝ), phi u * u ^ k := by
  have hi := (moment_integrable k).integral_prod_right
  have hs := intervalIntegral_integral_swap (a := (1 / 4 : ℝ)) (b := (1 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := momentKernel k)
    (by simpa only [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] using moment_integrable k)
  have he (w : ℝ) : (∫ t in (1 / 4 : ℝ)..1, momentKernel k t w) = mellin w * w ^ k := by
    unfold momentKernel MellinL2.mellin
    rw [intervalIntegral.integral_mul_const]
  constructor
  · change Integrable (fun w : ℝ => mellin w * w ^ k) (volume.restrict (Ioi 0))
    simpa only [Function.uncurry_apply_pair,
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1), he] using hi
  · simp_rw [← he]
    rw [← hs]
    calc
      _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t * t ^ k *
          ∫ u in Ioi (0 : ℝ), phi u * u ^ k := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        exact (moment_fiber k t (by linarith [ht.1])).2
      _ = _ := by rw [intervalIntegral.integral_mul_const, etaTwo_moment_compact]

#print axioms mellin_moment

/-- The actual quadratic Mellin moment in the calculation following 7.11. -/
theorem mellin_quadratic_moment (c : ℝ) :
    IntegrableOn (fun u : ℝ => (u - c) ^ 2 * mellin u) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), (u - c) ^ 2 * mellin u) =
        49 / 48 * Real.sqrt (Real.pi / 2) - 9 / 4 * c + c ^ 2 * Real.sqrt (Real.pi / 2) := by
  have h0 := MellinL1.mellin_integral
  have h1 := mellin_moment 1
  have h2 := mellin_moment 2
  norm_num [phi_first_moment] at h1
  norm_num [phi_second_moment] at h2
  have he : (fun u : ℝ => (u - c) ^ 2 * mellin u) =
      (fun u : ℝ => (mellin u * u ^ 2 - (2 * c) * (mellin u * u)) + c ^ 2 * mellin u) := by
    funext u
    ring
  rw [he]
  have hi := (h2.1.sub (h1.1.const_mul (2 * c))).add (h0.1.const_mul (c ^ 2))
  refine ⟨hi, ?_⟩
  have hiA : IntegrableOn (fun u : ℝ => mellin u * u ^ 2 - (2 * c) * (mellin u * u))
      (Ioi 0) := h2.1.sub (h1.1.const_mul _)
  rw [integral_add hiA (h0.1.const_mul _),
    integral_sub h2.1 (h1.1.const_mul _), integral_const_mul, integral_const_mul,
    h0.2, h1.2, h2.2]
  rw [Real.sqrt_div (by positivity)]
  ring

#print axioms mellin_quadratic_moment

/-- Positive kappa gives the cubic scaling factor in the page 58 quadratic moment. -/
theorem etaStar_quadratic_moment (k c : ℝ) (hk : 0 < k) :
    IntegrableOn (fun w : ℝ => (w - c / k) ^ 2 * etaStar k w) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), (w - c / k) ^ 2 * etaStar k w) =
        (49 / 48 * Real.sqrt (Real.pi / 2) - 9 / 4 * c + c ^ 2 * Real.sqrt (Real.pi / 2)) / k ^ 3 := by
  let g : ℝ → ℝ := fun u => (u - c) ^ 2 * mellin u
  have hi : IntegrableOn (fun w : ℝ => g (k * w)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hk).mpr
      (by simpa only [mul_zero] using (mellin_quadratic_moment c).1)
  have hs := integral_comp_mul_left_Ioi g 0 hk
  have he : (fun w : ℝ => (w - c / k) ^ 2 * etaStar k w) =
      (fun w : ℝ => g (k * w) / k ^ 2) := by
    funext w
    dsimp [g, etaStar]
    field_simp
    <;> ring
  rw [he]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div, hs]
  simp only [mul_zero, smul_eq_mul]
  change (k⁻¹ * (∫ u in Ioi (0 : ℝ), (u - c) ^ 2 * mellin u)) / k ^ 2 = _
  rw [(mellin_quadratic_moment c).2]
  field_simp

#print axioms etaStar_quadratic_moment

end LeanLab.Helfgott2013.MellinMoments
