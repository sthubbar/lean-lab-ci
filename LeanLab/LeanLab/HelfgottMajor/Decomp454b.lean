import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The scalar Gaussian tails in P0014 page 42, displays 4.37 to 4.39.
These estimates contain no zero count input.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454b
open Real MeasureTheory Set Filter
open scoped Topology

/-- Exact first Gaussian tail moment used in P0014 page 42, display 4.37. -/
theorem integral_mul_gaussian_Ioi (c T : ℝ) (hc : 0 < c) :
    (∫ t in Ioi T, t * exp (-c * t ^ 2)) = exp (-c * T ^ 2) / (2 * c) := by
  have hd (t : ℝ) : HasDerivAt (fun t => -(2 * c)⁻¹ * exp (-c * t ^ 2))
      (t * exp (-c * t ^ 2)) t := by
    convert (((hasDerivAt_pow 2 t).const_mul (-c)).exp).const_mul (-(2 * c)⁻¹)
      using 1
    field_simp
    ring
  have he : Tendsto (fun t : ℝ => exp (-c * t ^ 2)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (a := T)
    (fun t _ => hd t) (integrable_mul_exp_neg_mul_sq hc).integrableOn
    (he.const_mul (-(2 * c)⁻¹))
  convert hh using 1
  ring

/-- The Gaussian tail bound printed as display 4.37 on P0014 page 42.
Positive c and T avoid the zero denominators in the printed formula.
-/
theorem gaussian_tail_le (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    (∫ t in Ioi T, exp (-c * t ^ 2)) ≤ exp (-c * T ^ 2) / (2 * c * T) := by
  have hi : IntegrableOn (fun t : ℝ => (t * exp (-c * t ^ 2)) / T) (Ioi T) :=
    (integrable_mul_exp_neg_mul_sq hc).integrableOn.div_const T
  have hle : (∫ t in Ioi T, exp (-c * t ^ 2)) ≤
      ∫ t in Ioi T, (t * exp (-c * t ^ 2)) / T := by
    apply integral_mono_of_nonneg
    · filter_upwards with t
      positivity
    · exact hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply (le_div_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_right ht.le (exp_pos (-c * t ^ 2)).le]
  calc (∫ t in Ioi T, exp (-c * t ^ 2)) ≤
        ∫ t in Ioi T, (t * exp (-c * t ^ 2)) / T := hle
    _ = exp (-c * T ^ 2) / (2 * c * T) := by
      rw [integral_div, integral_mul_gaussian_Ioi c T hc]
      ring

/-- The reciprocal Gaussian tail bound in P0014 page 42, display 4.38.
Positive c and T give an absolutely convergent tail.
-/
theorem gaussian_tail_div_le (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    (∫ t in Ioi T, exp (-c * t ^ 2) / t) ≤
      exp (-c * T ^ 2) / (2 * c * T ^ 2) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-c * t ^ 2) / T) (Ioi T) :=
    (integrable_exp_neg_mul_sq hc).integrableOn.div_const T
  have hle : (∫ t in Ioi T, exp (-c * t ^ 2) / t) ≤
      ∫ t in Ioi T, exp (-c * t ^ 2) / T := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (exp_pos _).le (hT.trans ht).le
    · exact hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_le_div_of_nonneg_left (exp_pos _).le hT ht.le
  calc (∫ t in Ioi T, exp (-c * t ^ 2) / t) ≤
        (∫ t in Ioi T, exp (-c * t ^ 2)) / T := by
          simpa only [integral_div] using hle
    _ ≤ (exp (-c * T ^ 2) / (2 * c * T)) / T :=
      div_le_div_of_nonneg_right (gaussian_tail_le c T hc hT) hT.le
    _ = exp (-c * T ^ 2) / (2 * c * T ^ 2) := by ring

/-- The logarithmic Gaussian tail bound in P0014 page 42, display 4.39.
The source lower limit is at least e and the Gaussian coefficient is positive.
-/
theorem gaussian_tail_log_le (c T : ℝ) (hc : 0 < c) (hT : exp 1 ≤ T) :
    (∫ t in Ioi T, log t * exp (-c * t ^ 2)) ≤
      log T * exp (-c * T ^ 2) / (2 * c * T) := by
  have hT0 : 0 < T := (exp_pos 1).trans_le hT
  let G : ℝ → ℝ := fun t => -(log t * exp (-c * t ^ 2) / (2 * c * t))
  let D : ℝ → ℝ := fun t =>
    exp (-c * t ^ 2) * (log t + (log t - 1) / (2 * c * t ^ 2))
  have hd : ∀ t ∈ Ioi T, HasDerivAt G (D t) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hT0.trans ht).ne'
    have hl := hasDerivAt_log ht0
    have he := ((hasDerivAt_pow 2 t).const_mul (-c)).exp
    have hden := (hasDerivAt_id t).const_mul (2 * c)
    convert ((hl.mul he).div hden (by positivity : 2 * c * t ≠ 0)).neg using 1
    · rfl
    · dsimp only [D, id_eq, Pi.mul_apply]
      field_simp
      ring
  have hp : ∀ t ∈ Ioi T, 0 ≤ D t := by
    intro t ht
    have hl : 1 ≤ log t := (le_log_iff_exp_le (hT0.trans ht)).mpr (hT.trans ht.le)
    dsimp only [D]
    positivity
  have he : Tendsto (fun t : ℝ => exp (-c * t ^ 2)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hl : Tendsto (fun t : ℝ => log t / t) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hG : Tendsto G atTop (𝓝 0) := by
    have hh := (hl.mul he).div_const (2 * c) |>.neg
    convert hh using 1
    · funext t
      dsimp only [G]
      ring
    · norm_num
  have hcont : ContinuousWithinAt G (Ici T) T := by
    dsimp only [G]
    fun_prop (disch := positivity)
  have hi := integrableOn_Ioi_deriv_of_nonneg hcont hd hp hG
  have hv := integral_Ioi_of_hasDerivAt_of_nonneg hcont hd hp hG
  have hle : (∫ t in Ioi T, log t * exp (-c * t ^ 2)) ≤ ∫ t in Ioi T, D t := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hl : 1 ≤ log t := (le_log_iff_exp_le (hT0.trans ht)).mpr (hT.trans ht.le)
      positivity
    · exact hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hl : 1 ≤ log t := (le_log_iff_exp_le (hT0.trans ht)).mpr (hT.trans ht.le)
      have hx : 0 ≤ (log t - 1) / (2 * c * t ^ 2) := by positivity
      dsimp only [D]
      nlinarith [mul_nonneg (exp_pos (-c * t ^ 2)).le hx]
  calc (∫ t in Ioi T, log t * exp (-c * t ^ 2)) ≤ ∫ t in Ioi T, D t := hle
    _ = log T * exp (-c * T ^ 2) / (2 * c * T) := by
      rw [hv]
      dsimp only [G]
      ring

/-- Absolute convergence of the three Gaussian tails on P0014 page 42.
The logarithmic weight uses the same lower limit restriction as display 4.39.
-/
theorem gaussian_tail_weights_integrable (c T : ℝ) (hc : 0 < c) (hT : exp 1 ≤ T) :
    IntegrableOn (fun t => exp (-c * t ^ 2)) (Ioi T) ∧
    IntegrableOn (fun t => exp (-c * t ^ 2) / t) (Ioi T) ∧
    IntegrableOn (fun t => log t * exp (-c * t ^ 2)) (Ioi T) := by
  have hT0 : 0 < T := (exp_pos 1).trans_le hT
  have ht0 : ∀ t ∈ Ioi T, 0 < t := fun t ht => hT0.trans ht
  have ht1 : ∀ t ∈ Ioi T, 1 ≤ t := by
    intro t ht
    exact (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hT).trans ht.le
  refine ⟨(integrable_exp_neg_mul_sq hc).integrableOn, ?_, ?_⟩
  · apply ((integrable_exp_neg_mul_sq hc).integrableOn.div_const T).mono'
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      fun_prop (disch := exact (ht0 t ht).ne')
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htt := ht0 t ht
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ exp (-c * t ^ 2) / t)]
      exact div_le_div_of_nonneg_left (exp_pos _).le hT0 ht.le
  · apply (integrable_mul_exp_neg_mul_sq hc).integrableOn.mono'
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      fun_prop (disch := exact (ht0 t ht).ne')
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hl0 := log_nonneg (ht1 t ht)
      have hlt : log t ≤ t := by linarith [log_le_sub_one_of_pos (ht0 t ht)]
      rw [Real.norm_of_nonneg (mul_nonneg hl0 (exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right hlt (exp_pos _).le

end LeanLab.HelfgottMajor.Decomp454b
