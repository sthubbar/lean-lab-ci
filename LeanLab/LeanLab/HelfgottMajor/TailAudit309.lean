import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
Source audit of the monotone error cancellation on P0014 page 38 after display 4.28.
The explicit test is q equal to one, y equal to one and f of t equal to exp of minus t.
This disproves the printed cancellation identity, not the final zero sum estimate.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.TailAudit309
open Real MeasureTheory Set
open scoped Topology

/-- The positive comparison integral in the printed cancellation is at most exp of minus one.
Source P0014 page 38 after display 4.28, at q and y equal to one.
-/
theorem comparison_integral_le :
    (∫ t in Ioi (1 : ℝ), exp (-t) / t) ≤ exp (-1) := by
  rw [← integral_exp_neg_Ioi 1]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    exact div_nonneg (exp_pos _).le (by linarith)
  · exact integrableOn_exp_neg_Ioi 1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    exact div_le_self (exp_pos _).le (by linarith)

/-- The derivative contribution has the opposite sign from the claimed cancellation.
Source P0014 page 38 after display 4.28, with the actual g of display 4.25 at q equal to one.
-/
theorem derivative_integral_nonpos :
    (∫ t in Ioi (1 : ℝ), (-exp (-t)) * (0.5 * log t + 17.7)) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 < t at ht
  have hlog : 0 ≤ log t := log_nonneg (by linarith)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [exp_pos (-t)]) (by linarith)

/-- The printed monotone cancellation fails for the smooth decreasing exponential.
Source P0014 page 38 after display 4.28. This is a QUESTION about that proof step.
-/
theorem monotone_cancellation_fails :
    17.7 * exp (-1) -
      (∫ t in Ioi (1 : ℝ), (-exp (-t)) * (0.5 * log t + 17.7)) >
        0.5 * (∫ t in Ioi (1 : ℝ), exp (-t) / t) := by
  have h := comparison_integral_le
  have hneg := derivative_integral_nonpos
  have hpos := exp_pos (-1 : ℝ)
  linarith

/-- The exponential test satisfies the smoothness, monotonicity and decay assumptions.
Source P0014 page 37 Lemma 4.3 and page 38 after display 4.28.
-/
theorem exponential_admissible :
    ContDiff ℝ 1 (fun t : ℝ => exp (-t)) ∧
      Antitone (fun t : ℝ => exp (-t)) ∧
      Filter.Tendsto (fun t : ℝ => exp (-t) * t * log t)
        Filter.atTop (nhds 0) := by
  refine ⟨by fun_prop, ?_, ?_⟩
  · intro a b hab
    exact exp_le_exp.mpr (neg_le_neg hab)
  · have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 1 (by norm_num)
    have hlim' : Filter.Tendsto (fun t : ℝ => t ^ 2 * exp (-t)) Filter.atTop (nhds 0) := by
      simpa using hlim
    apply squeeze_zero' ?_ ?_ hlim'
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (mul_nonneg (exp_pos _).le (by linarith)) (log_nonneg ht)
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
      have hh := log_le_sub_one_of_pos (by linarith : 0 < t)
      have hm := mul_le_mul_of_nonneg_left (show log t ≤ t by linarith)
        (mul_nonneg (exp_pos (-t)).le (by linarith : 0 ≤ t))
      nlinarith

/-- The derivative error integral in the exponential test converges absolutely.
Source P0014 page 38 after display 4.28. This rules out a default divergent integral value.
-/
theorem derivative_integrable :
    IntegrableOn (fun t : ℝ => (-exp (-t)) * (0.5 * log t + 17.7)) (Ioi 1) := by
  have hp0 : IntegrableOn (fun t : ℝ => t * exp (-t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (1 : ℝ)) (p := (1 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  have hp := hp0.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have he := integrableOn_exp_neg_Ioi 1
  have hmajor := (hp.const_mul (0.5 : ℝ)).add (he.const_mul (17.7 : ℝ))
  apply hmajor.mono'
  · have hc : ContinuousOn (fun t : ℝ => (-exp (-t)) * (0.5 * log t + 17.7)) (Ioi 1) := by
      intro t ht
      change 1 < t at ht
      have ht0 : t ≠ 0 := by linarith
      fun_prop
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have hlog : 0 ≤ log t := log_nonneg (by linarith)
    have hupper : log t ≤ t := by linarith [log_le_sub_one_of_pos (by linarith : 0 < t)]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (exp_pos _),
      abs_of_nonneg (by linarith : 0 ≤ 0.5 * log t + 17.7)]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left hupper (exp_pos (-t)).le]

end LeanLab.HelfgottMajor.TailAudit309
