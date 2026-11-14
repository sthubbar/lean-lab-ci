/-
Jia 1996 page 281, first logarithmic integral in Lemma 27.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are elementary lower bounds for the numerical logarithmic kernel.
-/
import LeanLab.Languasco2004.Kernel548

namespace LeanLab.Languasco2004.LogKernel548
open Real Kernel548
noncomputable section

/-- Page 281 numerical support: a rational lower bound for log of nine fifths. -/
theorem log_nine_fifths_lower : (0.5877866 : ℝ) ≤ Real.log (9 / 5) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 2 / 7)
    (by norm_num : (2 / 7 : ℝ) < 1) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Page 281 numerical support: a rational logarithmic chord on nine fifths to two. -/
theorem log_chord_lower (y : ℝ) (hyL : 9 / 5 ≤ y) (hyU : y ≤ 2) :
    (0.6395421 : ℝ) + 0.5268025 * y ≤ 1 + Real.log y := by
  have ha : 0 ≤ 5 * (2 - y) := by linarith
  have hb : 0 ≤ 5 * (y - 9 / 5) := by linarith
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (9 / 5 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    ha hb (by ring : 5 * (2 - y) + 5 * (y - 9 / 5) = 1)
  simp only [smul_eq_mul] at hc
  have heq : 5 * (2 - y) * (9 / 5) + 5 * (y - 9 / 5) * 2 = y := by ring
  rw [heq] at hc
  have hlog2 : (0.6931471 : ℝ) ≤ Real.log 2 := le_of_lt
    (lt_trans (by norm_num) Real.log_two_gt_d9)
  have hcmp := add_le_add (mul_le_mul_of_nonneg_left log_nine_fifths_lower ha)
    (mul_le_mul_of_nonneg_left hlog2 hb)
  linarith

/-- Page 281: the logarithm argument throughout D30 lies between nine fifths and two. -/
theorem region30_log_argument (t u : ℝ)
    (htl : 34 / 99 ≤ t) (htu : t ≤ 1649 / 4752)
    (hul : 85 / 99 - 2 * t ≤ u) (huu : u ≤ 85 / 147 - 58 / 49 * t) :
    9 / 5 ≤ (1 - t - 2 * u) / u ∧ (1 - t - 2 * u) / u ≤ 2 := by
  have hu : 0 < u := by linarith
  constructor
  · apply (le_div_iff₀ hu).mpr
    linarith
  · apply (div_le_iff₀ hu).mpr
    linarith

/-- Page 281: a rational positive numerator minorizes the logarithmic kernel. -/
theorem region30_kernel_lower (t u : ℝ)
    (htl : 34 / 99 ≤ t) (htu : t ≤ 1649 / 4752)
    (hul : 85 / 99 - 2 * t ≤ u) (huu : u ≤ 85 / 147 - 58 / 49 * t) :
    0.6395421 / (t * u * (1 - t - u)) +
      0.5268025 * (1 - t - 2 * u) / (t * u ^ 2 * (1 - t - u)) ≤
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, _⟩ := region30_argument t u htl htu hul huu
  obtain ⟨hyL, hyU⟩ := region30_log_argument t u htl htu hul huu
  have h := log_chord_lower ((1 - t - 2 * u) / u) hyL hyU
  have he : (1 - t - 2 * u) / u = (1 - t) / u - 2 := by field_simp
  rw [he] at h
  have hd : 0 < t * u * (1 - t - u) := mul_pos (mul_pos ht hu) hv
  have hdiv := div_le_div_of_nonneg_right h hd.le
  convert hdiv using 1
  field_simp

#print axioms log_nine_fifths_lower
#print axioms log_chord_lower
#print axioms region30_log_argument
#print axioms region30_kernel_lower
end
end LeanLab.Languasco2004.LogKernel548
