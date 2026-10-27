/-
AI wrote this Lean code. Goldbach is open.
Source: Li 2024 v4 page 10, equation 20.
Explicit bounds for the normalized upper sieve correction near s = 3.
-/
import Mathlib

namespace LeanLab.Li2024.S5Bounds

open Real intervalIntegral

noncomputable def correction (y : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..y, Real.log (1 + v) / (2 + v)

theorem correction_bounds {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 / (2 * (1 + y) * (2 + y)) ≤ correction y ∧
      correction y ≤ y ^ 2 / 4 := by
  have hc : ContinuousOn (fun v : ℝ => Real.log (1 + v) / (2 + v)) (Set.Icc 0 y) := by
    apply ContinuousOn.div
    · exact (continuousOn_const.add continuousOn_id).log (by intro v hv; change 1 + v ≠ 0; linarith [hv.1])
    · exact continuousOn_const.add continuousOn_id
    · intro v hv; linarith [hv.1]
  have hi : IntervalIntegrable (fun v : ℝ => Real.log (1 + v) / (2 + v))
      MeasureTheory.volume 0 y := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hy] using hc
  have hp : 0 < (1 + y) * (2 + y) := by positivity
  have hlo : (∫ v in (0 : ℝ)..y, v / ((1 + y) * (2 + y))) ≤ correction y := by
    apply integral_mono_on hy ((continuous_id.div_const _).intervalIntegrable 0 y) hi
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hvy : v ≤ y := hv.2
    have hl := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + v)
    have hlog : v / (1 + v) ≤ Real.log (1 + v) := by
      convert hl using 1 <;> field_simp <;> ring
    have hden : (1 + v) * (2 + v) ≤ (1 + y) * (2 + y) := by nlinarith
    calc
      v / ((1 + y) * (2 + y)) ≤ v / ((1 + v) * (2 + v)) :=
        div_le_div_of_nonneg_left hv0 (by positivity) hden
      _ = (v / (1 + v)) / (2 + v) := by rw [div_div]
      _ ≤ Real.log (1 + v) / (2 + v) := div_le_div_of_nonneg_right hlog (by positivity)
  have hup : correction y ≤ ∫ v in (0 : ℝ)..y, v / 2 := by
    apply integral_mono_on hy hi ((continuous_id.div_const _).intervalIntegrable 0 y)
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + v)
    calc
      Real.log (1 + v) / (2 + v) ≤ v / (2 + v) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ v / 2 := div_le_div_of_nonneg_left hv0 (by norm_num) (by linarith)
  have hid : (∫ v in (0 : ℝ)..y, v) = y ^ 2 / 2 := by
    simp [integral_id]
  constructor
  · rw [integral_div, hid] at hlo
    simpa only [div_div, mul_assoc] using hlo
  · rw [integral_div, hid] at hup
    convert hup using 1 <;> ring

noncomputable def baseKernel (t : ℝ) : ℝ := 4 / (t * (57 / 64 - 5 / 2 * t))

theorem s5_base_integral :
    (∫ t in (1 / 4 : ℝ)..(57 / 224), baseKernel t) =
      (256 / 57) * Real.log (17 / 16) := by
  have hderiv : ∀ t ∈ Set.uIcc (1 / 4 : ℝ) (57 / 224),
      HasDerivAt (fun t => (256 / 57) * Real.log t -
        (256 / 57) * Real.log (57 / 64 - 5 / 2 * t)) (baseKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hd0 : (57 / 64 : ℝ) - 5 / 2 * t ≠ 0 := by linarith [ht.2]
    have h₁ := (Real.hasDerivAt_log ht0).const_mul (256 / 57)
    have h₂ := (((hasDerivAt_id t).const_mul (5 / 2)).const_sub
      (57 / 64)).log hd0
    have hh := h₁.sub (h₂.const_mul (256 / 57))
    convert hh using 1
    · rfl
    · dsimp [baseKernel]
      field_simp
      have he := inv_mul_cancel₀ (show (114 - t * 320) ≠ 0 by linarith [ht.2])
      linear_combination 256 * he
  have hint : IntervalIntegrable baseKernel MeasureTheory.volume (1 / 4) (57 / 224) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
    intro t ht
    apply mul_ne_zero
    · change t ≠ 0
      linarith [ht.1]
    · change (57 / 64 : ℝ) - 5 / 2 * t ≠ 0
      linarith [ht.2]
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hd₁ : (57 / 64 : ℝ) - 5 / 2 * (1 / 4) = 17 / 64 := by norm_num
  have hd₂ : (57 / 64 : ℝ) - 5 / 2 * (57 / 224) = 57 / 224 := by norm_num
  have he : Real.log (17 / 16) = Real.log (17 / 64) - Real.log (1 / 4) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hd₁, hd₂, he]
  ring

theorem s5_base_bounds :
    (0.27227900324 : ℝ) ≤ (256 / 57) * Real.log (17 / 16) ∧
      (256 / 57) * Real.log (17 / 16) ≤ 0.27227900325 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 17 : ℝ)) (by norm_num) 10
  have he : Real.log (1 - (1 / 17 : ℝ)) = -Real.log (17 / 16) := by
    rw [← Real.log_inv]
    norm_num
  rw [he, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem correction_continuous : ContinuousOn correction (Set.Icc 0 2) := by
  have hc : ContinuousOn (fun v : ℝ => Real.log (1 + v) / (2 + v))
      (Set.uIcc 0 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div
    · exact (continuousOn_const.add continuousOn_id).log (by
        intro v hv
        change 1 + v ≠ 0
        linarith [hv.1])
    · exact continuousOn_const.add continuousOn_id
    · intro v hv
      change 2 + v ≠ 0
      linarith [hv.1]
  have hh := continuousOn_primitive_interval' (μ := MeasureTheory.volume) hc.intervalIntegrable
    (show (0 : ℝ) ∈ Set.uIcc 0 2 by norm_num)
  change ContinuousOn (fun y => ∫ v in (0 : ℝ)..y, Real.log (1 + v) / (2 + v)) (Set.Icc 0 2)
  simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hh

noncomputable def excess (t : ℝ) : ℝ := 1149 / 100 * (57 / 64 - 5 / 2 * t) - 3

noncomputable def correctionKernel (t : ℝ) : ℝ :=
  baseKernel t * correction (max 0 (excess t))

theorem s5_correction_pointwise {t : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) (15431 / 61280)) :
    13.8 * (excess t) ^ 2 ≤ correctionKernel t ∧
      correctionKernel t ≤ 15.32 * (excess t) ^ 2 := by
  have hy : 0 ≤ excess t := by dsimp [excess]; linarith [ht.2]
  have hymax : excess t ≤ 333 / 6400 := by dsimp [excess]; linarith [ht.1]
  have hdlo : (3 / (1149 / 100) : ℝ) ≤ 57 / 64 - 5 / 2 * t := by linarith [ht.2]
  have hdhi : (57 / 64 : ℝ) - 5 / 2 * t ≤ 17 / 64 := by linarith [ht.1]
  have htpos : 0 < t := by linarith [ht.1]
  have hdpos : (0 : ℝ) < 57 / 64 - 5 / 2 * t := by linarith
  have hdenlo := mul_le_mul ht.1 hdlo (by norm_num : (0 : ℝ) ≤ 3 / (1149 / 100)) htpos.le
  have hdenhi := mul_le_mul ht.2 hdhi hdpos.le (by norm_num : (0 : ℝ) ≤ 15431 / 61280)
  have hb : (59.7 : ℝ) ≤ baseKernel t ∧ baseKernel t ≤ 61.28 := by
    dsimp [baseKernel]
    constructor
    · apply (le_div_iff₀ (mul_pos htpos hdpos)).mpr
      nlinarith [hdenhi]
    · apply (div_le_iff₀ (mul_pos htpos hdpos)).mpr
      nlinarith [hdenlo]
  have hq := correction_bounds hy
  have hqlo : (excess t) ^ 2 / 4.32 ≤ correction (excess t) := by
    apply le_trans _ hq.1
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (333 / 6400 - excess t)]
  have hqpos : 0 ≤ correction (excess t) :=
    (by positivity : 0 ≤ (excess t) ^ 2 / 4.32).trans hqlo
  have hlo := mul_le_mul hb.1 hqlo (by positivity : (0 : ℝ) ≤ (excess t) ^ 2 / 4.32) (by linarith [hb.1] : (0 : ℝ) ≤ baseKernel t)
  have hup := mul_le_mul hb.2 hq.2 hqpos (by norm_num : (0 : ℝ) ≤ 61.28)
  norm_num at hlo hup
  dsimp [correctionKernel]
  rw [max_eq_right hy]
  constructor <;> nlinarith [sq_nonneg (excess t)]

theorem s5_correction_integral_bounds :
    (0.0000225 : ℝ) ≤ ∫ t in (1 / 4 : ℝ)..(57 / 224), correctionKernel t ∧
      (∫ t in (1 / 4 : ℝ)..(57 / 224), correctionKernel t) ≤ 0.0000251 := by
  have hb : ContinuousOn baseKernel (Set.Icc (1 / 4) (57 / 224)) := by
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
    intro t ht
    apply mul_ne_zero
    · change t ≠ 0
      linarith [ht.1]
    · change (57 / 64 : ℝ) - 5 / 2 * t ≠ 0
      linarith [ht.2]
  have hm : Continuous (fun t : ℝ => max 0 (excess t)) := by unfold excess; fun_prop
  have hq : ContinuousOn (fun t => correction (max 0 (excess t)))
      (Set.Icc (1 / 4) (57 / 224)) := by
    apply correction_continuous.comp hm.continuousOn
    intro t ht
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      dsimp [excess]
      linarith [ht.1]
  have hc : ContinuousOn correctionKernel (Set.uIcc (1 / 4) (57 / 224)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact hb.mul hq
  have hi : IntervalIntegrable correctionKernel MeasureTheory.volume (1 / 4) (57 / 224) := hc.intervalIntegrable
  have hi₁ : IntervalIntegrable correctionKernel MeasureTheory.volume
      (1 / 4) (15431 / 61280) := hi.mono_set (by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩)
  have hi₂ : IntervalIntegrable correctionKernel MeasureTheory.volume
      (15431 / 61280) (57 / 224) := hi.mono_set (by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  have hz : (∫ t in (15431 / 61280 : ℝ)..(57 / 224), correctionKernel t) = 0 := by
    have he : Set.EqOn correctionKernel (fun _ => (0 : ℝ))
        (Set.uIcc (15431 / 61280) (57 / 224)) := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      have hy : excess t ≤ 0 := by dsimp [excess]; linarith [ht.1]
      simp [correctionKernel, max_eq_left hy, correction]
    rw [integral_congr he]
    simp
  have hp : (∫ t in (1 / 4 : ℝ)..(15431 / 61280), (excess t) ^ 2) =
      (333 / 6400 : ℝ) ^ 3 / (3 * (1149 / 100) * (5 / 2)) := by
    have hd : ∀ t : ℝ, HasDerivAt excess (-(1149 / 100) * (5 / 2)) t := by
      intro t
      have hh := (((((hasDerivAt_id t).const_mul (5 / 2)).const_sub
        (57 / 64)).const_mul (1149 / 100)).sub_const 3)
      convert hh using 1 <;> first | rfl | ring
    have hd₃ : ∀ t ∈ Set.uIcc (1 / 4 : ℝ) (15431 / 61280),
        HasDerivAt (fun t => -(excess t) ^ 3 / (3 * (1149 / 100) * (5 / 2)))
          ((excess t) ^ 2) t := by
      intro t ht
      convert (((hd t).pow 3).neg.div_const (3 * (1149 / 100) * (5 / 2))) using 1 <;> ring
    rw [integral_eq_sub_of_hasDerivAt hd₃ (by
      apply Continuous.intervalIntegrable
      unfold excess
      fun_prop)]
    norm_num [excess]
  have hlo := integral_mono_on (by norm_num : (1 / 4 : ℝ) ≤ 15431 / 61280)
    (show IntervalIntegrable (fun t : ℝ => 13.8 * (excess t) ^ 2)
      MeasureTheory.volume (1 / 4) (15431 / 61280) by
        apply Continuous.intervalIntegrable; unfold excess; fun_prop) hi₁
    (fun t ht => (s5_correction_pointwise ht).1)
  have hup := integral_mono_on (by norm_num : (1 / 4 : ℝ) ≤ 15431 / 61280) hi₁
    (show IntervalIntegrable (fun t : ℝ => 15.32 * (excess t) ^ 2)
      MeasureTheory.volume (1 / 4) (15431 / 61280) by
        apply Continuous.intervalIntegrable; unfold excess; fun_prop)
    (fun t ht => (s5_correction_pointwise ht).2)
  rw [integral_const_mul, hp] at hlo hup
  have he := integral_add_adjacent_intervals hi₁ hi₂
  rw [hz, add_zero] at he
  rw [← he]
  constructor <;> norm_num at * <;> linarith

noncomputable def directKernel (t : ℝ) : ℝ := baseKernel t + correctionKernel t

theorem s5_direct_enclosure :
    (0.2723015 : ℝ) ≤ (∫ t in (1 / 4 : ℝ)..(57 / 224), directKernel t) ∧
      (∫ t in (1 / 4 : ℝ)..(57 / 224), directKernel t) ≤ 0.2723042 := by
  have hb : ContinuousOn baseKernel (Set.uIcc (1 / 4) (57 / 224)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
    intro t ht
    apply mul_ne_zero
    · change t ≠ 0
      linarith [ht.1]
    · change (57 / 64 : ℝ) - 5 / 2 * t ≠ 0
      linarith [ht.2]
  have hm : Continuous (fun t : ℝ => max 0 (excess t)) := by unfold excess; fun_prop
  have hq : ContinuousOn (fun t => correction (max 0 (excess t)))
      (Set.uIcc (1 / 4) (57 / 224)) := by
    apply correction_continuous.comp hm.continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      dsimp [excess]
      linarith [ht.1]
  have hc : ContinuousOn correctionKernel (Set.uIcc (1 / 4) (57 / 224)) := hb.mul hq
  unfold directKernel
  rw [integral_add hb.intervalIntegrable hc.intervalIntegrable, s5_base_integral]
  have h₁ := s5_base_bounds
  have h₂ := s5_correction_integral_bounds
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

noncomputable def normalizedUpper (s : ℝ) : ℝ :=
  (1 + correction (max 0 (s - 3))) / s

theorem s5_kernel_eq {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) (57 / 224)) :
    directKernel t = 4 * (1149 / 100) *
      normalizedUpper ((1149 / 100) * (57 / 64 - 5 / 2 * t)) / t := by
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hd0 : (57 / 64 : ℝ) - 5 / 2 * t ≠ 0 := by linarith [ht.2]
  have alg (D q : ℝ) (hD : D ≠ 0) :
      4 / (t * D) + (4 / (t * D)) * q =
        4 * (1149 / 100) * ((1 + q) / ((1149 / 100) * D)) / t := by
    field_simp
    <;> ring
  exact alg _ _ hd0

theorem s5_direct_exceeds_print :
    (0.272301 : ℝ) < ∫ t in (1 / 4 : ℝ)..(57 / 224), directKernel t := by
  linarith [s5_direct_enclosure.1]

end LeanLab.Li2024.S5Bounds

#print axioms LeanLab.Li2024.S5Bounds.correction_bounds

#print axioms LeanLab.Li2024.S5Bounds.s5_base_integral

#print axioms LeanLab.Li2024.S5Bounds.s5_base_bounds

#print axioms LeanLab.Li2024.S5Bounds.correction_continuous

#print axioms LeanLab.Li2024.S5Bounds.s5_correction_pointwise

#print axioms LeanLab.Li2024.S5Bounds.s5_correction_integral_bounds

#print axioms LeanLab.Li2024.S5Bounds.s5_direct_enclosure

#print axioms LeanLab.Li2024.S5Bounds.s5_kernel_eq

#print axioms LeanLab.Li2024.S5Bounds.s5_direct_exceeds_print
