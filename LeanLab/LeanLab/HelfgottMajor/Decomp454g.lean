import LeanLab.HelfgottMajor.Decomp454a
import LeanLab.HelfgottMajor.TailAudit309

/-!
Positive instances and budget diagnostics for the assigned high tail route.
Source P0014 page 38 after display 4.28 and page 41 display 4.34.
These tests do not refute the sealed high zero mass estimate.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454g
open Real MeasureTheory Set Filter
open scoped Topology

/-- Exact positive exponential instance of the corrected page 38 error calculation.
The missing contribution is 35.4 times exp of minus one.
Source P0014 display 4.25 and the calculation after display 4.28.
-/
theorem exponential_error_exact :
    17.7 * exp (-1) -
      (∫ t in Ioi (1 : ℝ), (-exp (-t)) * (0.5 * log t + 17.7)) =
        35.4 * exp (-1) + 0.5 * ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  have hf (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have hft : IntegrableOn (fun t : ℝ => exp (-t) / t) (Ioi 1) := by
    apply (integrableOn_exp_neg_Ioi 1).mono'
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      have ht1 : 1 < t := ht
      have ht0 : t ≠ 0 := by linarith
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := by linarith
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ exp (-t) / t)]
      exact div_le_self (exp_pos _).le ht.le
  have he : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero
  have hl : Tendsto (fun t : ℝ => exp (-t) * log t) atTop (𝓝 0) := by
    have hh := TailAudit309.exponential_admissible.2.2.mul tendsto_inv_atTop_zero
    apply (show Tendsto (fun t : ℝ => (exp (-t) * t * log t) * t⁻¹) atTop (𝓝 0) by
      simpa using hh).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have hend : Tendsto (fun t : ℝ => exp (-t) * (0.5 * log (1 * t) + 17.7)) atTop (𝓝 0) := by
    have hh := (hl.const_mul 0.5).add (he.const_mul 17.7)
    convert hh using 1
    · funext t
      simp only [one_mul]
      ring
    · norm_num
  have hstart : Tendsto (fun t : ℝ => exp (-t) * (0.5 * log (1 * t) + 17.7))
      (𝓝[>] 1) (𝓝 (exp (-1) * (0.5 * log (1 * 1) + 17.7))) := by
    have hc : ContinuousAt (fun t : ℝ => exp (-t) * (0.5 * log (1 * t) + 17.7)) 1 := by
      fun_prop (disch := norm_num)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hh := Decomp454a.logarithmic_error_boundary (fun t => exp (-t)) (fun t => -exp (-t))
    1 1 (by norm_num) (by norm_num) (fun t _ => hf t) hft
    (by simpa using TailAudit309.derivative_integrable) hstart hend
  norm_num only [one_mul, log_one, mul_zero, zero_add] at hh
  nlinarith [hh]

/-- The coarse fourth power budget exceeds the printed exponential envelope at height 100.
Source P0014 page 41 display 4.34. This is a limitation of the new coarse route.
-/
theorem coarse_decay_budget_too_large :
    4.226 * exp (-0.1598 * (100 : ℝ)) < 384 / (100 : ℝ) ^ 4 := by
  have he := Real.sum_le_exp_of_nonneg (x := (0.1598 * 100 : ℝ)) (by norm_num) 16
  norm_num at he
  have hpos : 0 < exp (0.1598 * (100 : ℝ)) := exp_pos _
  rw [show (-0.1598 * (100 : ℝ)) = -(0.1598 * 100) by ring, exp_neg]
  apply (mul_inv_lt_iff₀ hpos).mpr
  norm_num
  linarith [he]

end LeanLab.HelfgottMajor.Decomp454g
