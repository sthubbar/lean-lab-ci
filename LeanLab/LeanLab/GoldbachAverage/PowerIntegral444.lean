import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
A single oscillatory power integral used in the BHMS pair expansions.
Source: https://arxiv.org/abs/1704.06103v2 pages 18 and 19.
The explicit constant below is derived and is not printed in the source.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.PowerIntegral444
open MeasureTheory Complex Set

/-- BHMS pages 18 and 19, a single power has reciprocal ordinate decay on a dyadic enlargement.
The exponent real part only needs an upper bound of two. -/
theorem power_integral_bound (w : ℂ) (hw : w.re ≤ 2) (x : ℝ) (hx : 0 < x) :
    ‖∫ u in x..(3 * x), (u : ℂ) ^ w‖ ≤
      56 * x ^ (w.re + 1) / (1 + |w.im|) := by
  have hden : 0 < 1 + |w.im| := by positivity
  have hX : 0 < x ^ (w.re + 1) := Real.rpow_pos_of_pos hx _
  have hxp : x ^ w.re * x = x ^ (w.re + 1) := (Real.rpow_add_one hx.ne' _).symm
  have hpt (u : ℝ) (hu : u ∈ Set.uIoc x (3 * x)) :
      ‖(u : ℂ) ^ w‖ ≤ 9 * x ^ w.re := by
    rw [Set.uIoc_of_le (by linarith : x ≤ 3 * x)] at hu
    have hu0 : 0 < u := lt_trans hx hu.1
    have hratio1 : 1 ≤ u / x := (le_div_iff₀ hx).mpr (by linarith [hu.1])
    have hratio3 : u / x ≤ 3 := (div_le_iff₀ hx).mpr hu.2
    have hr := Real.rpow_le_rpow_of_exponent_le hratio1 hw
    have hsq : (u / x) ^ (2 : ℝ) ≤ 9 := by
      rw [Real.rpow_two]
      nlinarith
    rw [Real.div_rpow hu0.le hx.le] at hr
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hq : u ^ w.re / x ^ w.re ≤ 9 := hr.trans hsq
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mp hq
  have hrough := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_pos (by linarith : 0 < 3 * x - x)] at hrough
  have hrough' : ‖∫ u in x..(3 * x), (u : ℂ) ^ w‖ ≤ 18 * x ^ (w.re + 1) := by
    calc _ ≤ 9 * x ^ w.re * (3 * x - x) := hrough
      _ = 18 * (x ^ w.re * x) := by ring
      _ = _ := by rw [hxp]
  by_cases him : |w.im| ≤ 1
  · apply hrough'.trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hX.le (sub_nonneg.mpr him)]
  · have him1 : 1 < |w.im| := lt_of_not_ge him
    have him0 : 0 < |w.im| := by linarith
    have hne : w ≠ -1 := by
      intro he
      norm_num [he] at him1
    have hzero : (0 : ℝ) ∉ Set.uIcc x (3 * x) := by
      rw [Set.uIcc_of_le (by linarith : x ≤ 3 * x)]
      simp only [mem_Icc, not_and]
      intro h
      linarith
    rw [integral_cpow (Or.inr ⟨hne, hzero⟩), norm_div]
    have hscale : (3 * x) ^ (w.re + 1) ≤ 27 * x ^ (w.re + 1) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hx.le]
      have hb : (3 : ℝ) ^ (w.re + 1) ≤ 27 := by
        calc _ ≤ (3 : ℝ) ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 27 := by norm_num
      exact mul_le_mul_of_nonneg_right hb hX.le
    have hnum : ‖(↑(3 * x) : ℂ) ^ (w + 1) - (x : ℂ) ^ (w + 1)‖ ≤
        28 * x ^ (w.re + 1) := by
      have hn := norm_sub_le ((↑(3 * x) : ℂ) ^ (w + 1)) ((x : ℂ) ^ (w + 1))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re] at hn
      linarith
    have hnorm : |w.im| ≤ ‖w + 1‖ := by
      simpa only [Complex.add_im, Complex.one_im, add_zero] using Complex.abs_im_le_norm (w + 1)
    have hnpos : 0 < ‖w + 1‖ := lt_of_lt_of_le him0 hnorm
    calc _ ≤ (28 * x ^ (w.re + 1)) / ‖w + 1‖ :=
          div_le_div_of_nonneg_right hnum hnpos.le
      _ ≤ (28 * x ^ (w.re + 1)) / |w.im| :=
          div_le_div_of_nonneg_left (by positivity) him0 hnorm
      _ ≤ _ := by
        apply (div_le_div_iff₀ him0 hden).mpr
        nlinarith [mul_nonneg hX.le (sub_nonneg.mpr him1.le)]

end LeanLab.GoldbachAverage.PowerIntegral444
