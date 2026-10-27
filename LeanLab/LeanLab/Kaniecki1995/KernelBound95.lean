/-
P0022, pages 365 and 366, the low height kernel estimate.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.ExpRatio95
import LeanLab.Kaniecki1995.Section3

namespace LeanLab.Kaniecki1995.KernelBound95
open Real Complex MeasureTheory

/-- Pages 365 and 366. The exponential kernel quotient is uniformly bounded
when half the norm of its argument is at most 7.02. -/
theorem quotient_low {T : ℝ} (hT : 7.02 < T) {s : ℂ} (hs : ‖s‖ / 2 ≤ 7.02) :
    ‖(Complex.exp ((Real.log (1 + 1 / T) : ℂ) * s) - 1) / s‖ ≤
      1 / (T * (1 - 7.02 / T)) := by
  have hT0 : 0 < T := by linarith
  let δ := Real.log (1 + 1 / T)
  have hδ0 : 0 ≤ δ := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hδ := delta_le hT0
  change δ ≤ 1 / T at hδ
  have hsmall : δ * ‖s‖ / 2 ≤ 7.02 / T := by
    calc δ * ‖s‖ / 2 ≤ (1 / T) * (‖s‖ / 2) := by nlinarith [norm_nonneg s]
      _ ≤ (1 / T) * 7.02 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 7.02 / T := by ring
  have hden : 0 < 1 - 7.02 / T := by
    have : 7.02 / T < 1 := (div_lt_one hT0).mpr hT
    linarith
  have h := ExpRatio95.exp_scaled_bound hδ0 (s := s) (by linarith)
  calc ‖(Complex.exp ((δ : ℂ) * s) - 1) / s‖ ≤ δ / (1 - δ * ‖s‖ / 2) := h
    _ ≤ (1 / T) / (1 - 7.02 / T) :=
      div_le_div₀ (by positivity) hδ hden (by linarith)
    _ = 1 / (T * (1 - 7.02 / T)) := by rw [div_div]

/-- Pages 365 and 366. The squared kernel bound holds up to height 14. -/
theorem kern_low {T σ t : ℝ} (hT : 7.02 < T) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 3 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    kern T σ t ≤ (1 / (T * (1 - 7.02 / T))) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply quotient_low hT
  have h := c702 hσ0 hσ ht0 ht
  have heq : ‖(σ : ℂ) + t * I‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply, pow_two]
  rw [heq]
  exact h.le

/-- Pages 365 and 366. A supplied norm bound M gives the low height integral bound.
This theorem does not assert a norm bound for the logarithmic derivative. -/
theorem low_integral {T σ M : ℝ} (hT : 7.02 < T) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 3 / 4)
    (hM : 0 ≤ M) (F : ℝ → ℂ) (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 14, ‖F t‖ ≤ M) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 14, ENNReal.ofReal (kern T σ t * ‖F t‖ ^ 2)) ≤
      ENNReal.ofReal (14 * M ^ 2 / (T ^ 2 * (1 - 7.02 / T) ^ 2)) := by
  let C : ℝ := 1 / (T * (1 - 7.02 / T))
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 7.02 / T := by
    have h : 7.02 / T < 1 := (div_lt_one hT0).mpr hT
    linarith
  calc (∫⁻ t in Set.Ioo (0 : ℝ) 14, ENNReal.ofReal (kern T σ t * ‖F t‖ ^ 2)) ≤
      ∫⁻ _t in Set.Ioo (0 : ℝ) 14, ENNReal.ofReal (C ^ 2 * M ^ 2) := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable (ae_of_all _ fun t ht => ?_)
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul (kern_low hT hσ0 hσ ht.1.le ht.2.le)
          (pow_le_pow_left₀ (norm_nonneg _) (hF t ht) 2) (sq_nonneg _) (sq_nonneg _)
    _ = ENNReal.ofReal (C ^ 2 * M ^ 2) * ENNReal.ofReal 14 := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      norm_num
    _ = ENNReal.ofReal (14 * M ^ 2 / (T ^ 2 * (1 - 7.02 / T) ^ 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [C]
      field_simp
      <;> ring

/-- Pages 365 and 366. A concrete point in the low height parameter range. -/
theorem low_parameter_instance :
    (7.02 : ℝ) < 10 ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 3 / 4 ∧
      (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 14 := by norm_num

end LeanLab.Kaniecki1995.KernelBound95

#print axioms LeanLab.Kaniecki1995.KernelBound95.quotient_low
#print axioms LeanLab.Kaniecki1995.KernelBound95.kern_low

#print axioms LeanLab.Kaniecki1995.KernelBound95.low_integral

#print axioms LeanLab.Kaniecki1995.KernelBound95.low_parameter_instance
