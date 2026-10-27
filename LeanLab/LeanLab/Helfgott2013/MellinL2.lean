/-
Cauchy Schwarz inputs for Helfgott, arXiv:1312.7748v2, printed page 61.
These prove the analytic steps behind the constant 1.77082 before 7.24.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.GaussianL2
import LeanLab.Helfgott2013.EtaTwo
import LeanLab.Helfgott2013.SectionSevenI

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.MellinL2

/-- Cauchy Schwarz against the constant function on a compact interval. -/
theorem interval_cauchy_schwarz {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  let I : ℝ := ∫ t in a..b, f t
  let Q : ℝ := ∫ t in a..b, f t ^ 2
  let c : ℝ := I / (b - a)
  have hv : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun t => sq_nonneg _)
  have he : (∫ t in a..b, (f t - c) ^ 2) = Q - 2 * c * I + (b - a) * c ^ 2 := by
    calc
      _ = ∫ t in a..b, (f t ^ 2 - 2 * c * f t) + c ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hf2 (hf.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        rfl
  have hlen : 0 < b - a := sub_pos.mpr hab
  have halg : Q - 2 * c * I + (b - a) * c ^ 2 = Q - I ^ 2 / (b - a) := by
    dsimp [c]
    field_simp
    <;> ring
  rw [he, halg] at hv
  have h := (div_le_iff₀ hlen).mp (show I ^ 2 / (b - a) ≤ Q by linarith)
  simpa only [I, Q, mul_comm] using h

#print axioms interval_cauchy_schwarz

open EtaTwo GaussianL2

/-- The unscaled Mellin convolution, with eta2 restricted to its support. -/
noncomputable def mellin (w : ℝ) : ℝ :=
  ∫ t in (1 / 4 : ℝ)..1, etaTwo t * phi (w / t) / t

/-- Pointwise Cauchy Schwarz gives the support length factor three quarters. -/
theorem mellin_sq_le (w : ℝ) :
    mellin w ^ 2 ≤ 3 / 4 *
      ∫ t in (1 / 4 : ℝ)..1, etaTwo t ^ 2 * phi (w / t) ^ 2 / t ^ 2 := by
  have ht0 : ∀ t ∈ Icc (1 / 4 : ℝ) 1, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hp : Continuous phi := by unfold phi; fun_prop
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * phi (w / t) / t)
      (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.mul (hp.comp_continuousOn
      (continuousOn_const.div continuousOn_id ht0))).div continuousOn_id ht0
  have hs := interval_cauchy_schwarz (by norm_num : (1 / 4 : ℝ) < 1) _
    (hc.intervalIntegrable_of_Icc (by norm_num))
    ((hc.pow 2).intervalIntegrable_of_Icc (by norm_num))
  have he : (∫ t in (1 / 4 : ℝ)..1, (etaTwo t * phi (w / t) / t) ^ 2) =
      ∫ t in (1 / 4 : ℝ)..1, etaTwo t ^ 2 * phi (w / t) ^ 2 / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  norm_num only at hs
  rw [he] at hs
  convert hs using 1 <;> norm_num [mellin]

#print axioms mellin_sq_le

/-- The nonnegative squared kernel that majorizes the Mellin norm. -/
noncomputable def sqKernel (t w : ℝ) : ℝ := etaTwo t ^ 2 * phi (w / t) ^ 2 / t ^ 2

/-- Scaling the inner Gaussian integral, with integrability included. -/
theorem kernel_fiber (t : ℝ) (ht : 0 < t) :
    IntegrableOn (sqKernel t) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), sqKernel t w) = etaTwo t ^ 2 / t * (3 / 8 * Real.sqrt Real.pi) := by
  have hint : IntegrableOn (fun w : ℝ => phi (w / t) ^ 2) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_right_iff (fun w : ℝ => phi w ^ 2)
      0 (inv_pos.mpr ht)).mpr (by simpa using phi_sq_integrable)
    simpa only [div_eq_mul_inv] using h
  have he : (∫ w in Ioi (0 : ℝ), phi (w / t) ^ 2) = t * (3 / 8 * Real.sqrt Real.pi) := by
    have h := integral_comp_mul_right_Ioi (fun w : ℝ => phi w ^ 2) 0 (inv_pos.mpr ht)
    simpa only [zero_mul, inv_inv, smul_eq_mul, phi_sq_integral, div_eq_mul_inv] using h
  have hfun : sqKernel t = fun w : ℝ => (etaTwo t ^ 2 / t ^ 2) * phi (w / t) ^ 2 := by
    funext w
    unfold sqKernel
    ring
  constructor
  · rw [hfun]
    exact hint.const_mul _
  · rw [hfun, integral_const_mul, he]
    field_simp
    <;> ring

#print axioms kernel_fiber

/-- The squared kernel is integrable on the product domain, so Fubini applies. -/
theorem kernel_integrable : Integrable (Function.uncurry sqKernel)
    ((volume.restrict (Ioc (1 / 4 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have heta : Measurable etaTwo := by
    have h : Measurable (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0) := by
      fun_prop
    exact Measurable.ite measurableSet_Ioi h measurable_const
  have hp : Continuous phi := by unfold phi; fun_prop
  have hm : Measurable (Function.uncurry sqKernel) :=
    (((heta.comp measurable_fst).pow_const 2).mul
      ((hp.measurable.comp (measurable_snd.div measurable_fst)).pow_const 2)).div
        (measurable_fst.pow_const 2)
  have hc : ContinuousOn (fun t : ℝ => etaTwo t ^ 2 / t * (3 / 8 * Real.sqrt Real.pi))
      (Icc (1 / 4 : ℝ) 1) :=
    ((continuousOn_etaTwo.pow 2).div continuousOn_id (by
      intro t ht
      change t ≠ 0
      linarith [ht.1])).mul_const _
  have ho : IntegrableOn (fun t : ℝ => etaTwo t ^ 2 / t * (3 / 8 * Real.sqrt Real.pi))
      (Ioc (1 / 4 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (hc.intervalIntegrable_of_Icc (by norm_num))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact (kernel_fiber t (by linarith [ht.1])).1
  · apply ho.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have hn (w : ℝ) : ‖sqKernel t w‖ = sqKernel t w := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold sqKernel
      positivity
    simp only [Function.uncurry_apply_pair]
    simp_rw [hn]
    exact (kernel_fiber t (by linarith [ht.1])).2.symm

#print axioms kernel_integrable

/-- Fubini and scaling evaluate the full squared kernel majorant. -/
theorem kernel_total :
    IntegrableOn (fun w : ℝ => ∫ t in (1 / 4 : ℝ)..1, sqKernel t w) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), ∫ t in (1 / 4 : ℝ)..1, sqKernel t w) =
        (32 / 3 * Real.log 2 ^ 3) * (3 / 8 * Real.sqrt Real.pi) := by
  have hi := kernel_integrable.integral_prod_right
  have hc : ∀ w : ℝ, (∫ t in (1 / 4 : ℝ)..1, sqKernel t w) =
      ∫ t in Ioc (1 / 4 : ℝ) 1, sqKernel t w := by
    intro w
    rw [intervalIntegral.integral_of_le (by norm_num)]
  have hs := intervalIntegral_integral_swap (a := (1 / 4 : ℝ)) (b := (1 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ))) (f := sqKernel)
    (by simpa only [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] using kernel_integrable)
  constructor
  · change Integrable (fun w : ℝ => ∫ t in (1 / 4 : ℝ)..1, sqKernel t w)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [hc, Function.uncurry_apply_pair] using hi
  · rw [← hs]
    calc
      _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t ^ 2 / t * (3 / 8 * Real.sqrt Real.pi) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num)] at ht
        dsimp only
        exact (kernel_fiber t (by linarith [ht.1])).2
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, etaTwo_sq_moment_compact]

#print axioms kernel_total

/-- The integrated Cauchy Schwarz bound, including integrability of the convolution square. -/
theorem mellin_sq_integral :
    IntegrableOn (fun w : ℝ => mellin w ^ 2) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), mellin w ^ 2) ≤
        3 / 4 * ((32 / 3 * Real.log 2 ^ 3) * (3 / 8 * Real.sqrt Real.pi)) := by
  have heta : Measurable etaTwo := by
    have h : Measurable (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0) := by
      fun_prop
    exact Measurable.ite measurableSet_Ioi h measurable_const
  have hp : Continuous phi := by unfold phi; fun_prop
  have hj : Measurable (fun p : ℝ × ℝ => etaTwo p.1 * phi (p.2 / p.1) / p.1) :=
    ((heta.comp measurable_fst).mul
      (hp.measurable.comp (measurable_snd.div measurable_fst))).div measurable_fst
  have hm : StronglyMeasurable mellin := by
    change StronglyMeasurable (fun w : ℝ =>
      ∫ t in (1 / 4 : ℝ)..1, etaTwo t * phi (w / t) / t)
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    exact hj.stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Ioc (1 / 4 : ℝ) 1))
  have hb (w : ℝ) : mellin w ^ 2 ≤ 3 / 4 * ∫ t in (1 / 4 : ℝ)..1, sqKernel t w := by
    exact mellin_sq_le w
  have hi := kernel_total.1.const_mul (3 / 4 : ℝ)
  have hm2 : IntegrableOn (fun w : ℝ => mellin w ^ 2) (Ioi 0) :=
    hi.mono_nonneg ((hm.measurable.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun w => sq_nonneg _))
      (Filter.Eventually.of_forall hb)
  refine ⟨hm2, ?_⟩
  have h := integral_mono hm2 hi hb
  rwa [integral_const_mul, kernel_total.2] at h

#print axioms mellin_sq_integral

/-- The paper's numerical coefficient for the unscaled squared norm. -/
theorem mellin_sq_integral_le :
    (∫ w in Ioi (0 : ℝ), mellin w ^ 2) ≤ (1.77082 : ℝ) := by
  apply mellin_sq_integral.2.trans
  convert LeanLab.Helfgott2013.eta_star_two using 1 <;> ring

#print axioms mellin_sq_integral_le

/-- The support integral equals the paper's full positive Mellin convolution. -/
theorem mellin_eq_halfline (w : ℝ) :
    mellin w = ∫ t in Ioi (0 : ℝ), etaTwo t * phi (w / t) / t := by
  have hs : ∀ t : ℝ, t ∉ Icc (1 / 4 : ℝ) 1 → etaTwo t * phi (w / t) / t = 0 := by
    intro t ht
    rw [etaTwo_eq_zero ht]
    simp
  have hp : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → etaTwo t * phi (w / t) / t = 0 := by
    intro t ht
    apply hs
    simp only [mem_Ioi, not_lt] at ht
    intro hmem
    linarith [hmem.1]
  calc
    _ = ∫ t in Icc (1 / 4 : ℝ) 1, etaTwo t * phi (w / t) / t := by
      unfold mellin
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    _ = ∫ t : ℝ, etaTwo t * phi (w / t) / t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hs
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero hp).symm

#print axioms mellin_eq_halfline

/-- The scaled smoothing function in the paper. -/
noncomputable def etaStar (k w : ℝ) : ℝ := mellin (k * w)

/-- The full page 61 squared norm bound for every positive scaling parameter. -/
theorem etaStar_sq_integral (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun w : ℝ => etaStar k w ^ 2) (Ioi 0) ∧
      (∫ w in Ioi (0 : ℝ), etaStar k w ^ 2) ≤ 1.77082 / k := by
  have hi : IntegrableOn (fun w : ℝ => mellin (k * w) ^ 2) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun w : ℝ => mellin w ^ 2) 0 hk).mpr
      (by simpa only [mul_zero] using mellin_sq_integral.1)
  have hs : (∫ w in Ioi (0 : ℝ), etaStar k w ^ 2) =
      k⁻¹ * ∫ w in Ioi (0 : ℝ), mellin w ^ 2 := by
    simpa only [etaStar, mul_zero, smul_eq_mul] using
      integral_comp_mul_left_Ioi (fun w : ℝ => mellin w ^ 2) 0 hk
  refine ⟨hi, ?_⟩
  calc
    _ = k⁻¹ * ∫ w in Ioi (0 : ℝ), mellin w ^ 2 := hs
    _ ≤ k⁻¹ * 1.77082 := mul_le_mul_of_nonneg_left mellin_sq_integral_le (inv_nonneg.mpr hk.le)
    _ = 1.77082 / k := by ring

#print axioms etaStar_sq_integral

end LeanLab.Helfgott2013.MellinL2
