import LeanLab.HelfgottMajor.Decomp431b
import LeanLab.HelfgottMajor.Decomp431c
import LeanLab.HelfgottMajor.Continuation457

/-!
Two elementary Cauchy Schwarz supplies from the remaining sorry inventory.
Source book Part IV page 434, the step before and after display 16.26.
The signed zero sampling and cutoff boundary inputs remain OPEN.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Sampling457
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs Decomp269a Decomp389b
open scoped Topology FourierTransform

/-- Interval Cauchy Schwarz with the first square energy extended to the upper half line.
Derived bookkeeping for the two continuous integrals on book page 434.
-/
theorem interval_mul_le_energy (f g : ℝ → ℝ) (a T : ℝ) (ha : a ≤ 1) (hT : 1 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioi a))) (hg : ContinuousOn g (Icc 1 T)) :
    (∫ t in (1 : ℝ)..T, f t * g t) ≤
      sqrt (∫ t in Ioi a, f t ^ 2) * sqrt (∫ t in (1 : ℝ)..T, g t ^ 2) := by
  have hfI : MemLp f 2 (volume.restrict (Ioc 1 T)) :=
    hf.mono_measure (Measure.restrict_mono (fun t ht => lt_of_le_of_lt ha ht.1) le_rfl)
  have hgI : MemLp g 2 (volume.restrict (Ioc 1 T)) := by
    apply (memLp_two_iff_integrable_sq_norm
      ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
    exact ((hg.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcmp : (∫ t in Ioc (1 : ℝ) T, f t * g t) ≤
      ∫ t in Ioc (1 : ℝ) T, ‖f t‖ * ‖g t‖ := by
    apply integral_mono_ae (hfI.integrable_mul hgI) (hfI.norm.integrable_mul hgI.norm)
    filter_upwards [] with t
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using! le_abs_self (f t * g t)
  have hcs := integral_mul_norm_le_Lp_mul_Lq (f := f) (g := g)
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (by simpa using hfI) (by simpa using hgI)
  simp only [Real.norm_eq_abs, rpow_two, sq_abs, ← sqrt_eq_rpow] at hcs
  have hfi : IntegrableOn (fun t : ℝ => f t ^ 2) (Ioi a) := by
    simpa only [Real.norm_eq_abs, sq_abs] using!
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have he : (∫ t in Ioc (1 : ℝ) T, f t ^ 2) ≤ ∫ t in Ioi a, f t ^ 2 := by
    apply setIntegral_mono_set hfi (Eventually.of_forall fun t => sq_nonneg (f t))
    exact Eventually.of_forall fun t ht => lt_of_le_of_lt ha ht.1
  simp only [intervalIntegral.integral_of_le hT]
  exact (hcmp.trans hcs).trans (mul_le_mul_of_nonneg_right
    (sqrt_le_sqrt he) (sqrt_nonneg _))

/-- Exactly the main weight Cauchy Schwarz sibling leaf, with no zero count hypothesis.
Source book page 434, Cauchy Schwarz before display 16.26.
-/
theorem main_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
  have hc : Continuous (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + t * Complex.I)
      (Continuation457.gaussian_mellin_differentiable δ _ (by norm_num)).continuousAt
      (by fun_prop)
  have hf : MemLp (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc.norm.aestronglyMeasurable).mpr
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
      Decomp431b.gaussian_line_integrable δ
  have hg : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t / (2 * π))) (Icc 1 T) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log (by fun_prop)
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    exact ne_of_gt (by have := ht.1; positivity)
  have hh := interval_mul_le_energy _ _ 0 T (by norm_num) hT (hf.mono_measure Measure.restrict_le_self) hg
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1 / (2 * π))
  simpa only [lineEnergy, one_mul, mul_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hm

/-- Exactly the derivative weight Cauchy Schwarz sibling leaf, with no zero count hypothesis.
Source book page 434, differentiated Plancherel after display 16.26.
-/
theorem error_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) ≤
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  have hc : Continuous (fun t : ℝ => deriv (gaussianMellin δ) ((1 / 2 : ℂ) + t * Complex.I)) := by
    simp_rw [MellinDerivative431.derivative_eq_fourier]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (MellinDerivative431.logWeightedGaussian_integrable δ)).comp
      (by fun_prop)
  have hf : MemLp (fun t : ℝ => ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + t * Complex.I)‖) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc.norm.aestronglyMeasurable).mpr
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
      Decomp431c.gaussian_derivative_line_integrable δ
  have hg : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389) (Icc 1 T) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have ht0 : 0 < t := by have := ht.1; linarith
    fun_prop (disch := positivity)
  have hh := interval_mul_le_energy _ _ 1 T le_rfl hT (hf.mono_measure Measure.restrict_le_self) hg
  simpa only [derivativeEnergy, one_mul] using hh

end LeanLab.HelfgottMajor.Sampling457

#print axioms LeanLab.HelfgottMajor.Sampling457.interval_mul_le_energy
#print axioms LeanLab.HelfgottMajor.Sampling457.main_weight_cauchy_schwarz
#print axioms LeanLab.HelfgottMajor.Sampling457.error_weight_cauchy_schwarz
