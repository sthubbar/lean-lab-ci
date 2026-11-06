import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The interval Cauchy Schwarz step on BHMS page 18 before expanding the low zero square.
Source: https://arxiv.org/abs/1704.06103v2 page 18 first display.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WindowCauchy444
open MeasureTheory Filter

/-- BHMS page 18 first display, the complex integral square costs the interval length.
This reuses Mathlib Holder with exponents two and two. -/
theorem norm_integral_square_le (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) :
    ‖∫ u in a..b, f u‖ ^ 2 ≤ (b - a) * ∫ u in a..b, ‖f u‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hg : MemLp (fun u => ‖f u‖) (ENNReal.ofReal 2) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hf.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    exact MemLp.of_bound measurable_const.aestronglyMeasurable 1
      (Eventually.of_forall fun _ => by simp)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall fun u => norm_nonneg (f u))
    (Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hg hone
  norm_num only [Real.rpow_two, one_pow, mul_one] at hHolder
  have hOneInt : (∫ _u, (1 : ℝ) ∂μ) = b - a := by
    change (∫ _u in Set.Ioc a b, (1 : ℝ)) = b - a
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul,
      mul_one]
  rw [hOneInt, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHolder
  have hcs : (∫ u in a..b, ‖f u‖) ≤
      Real.sqrt (∫ u in a..b, ‖f u‖ ^ 2) * Real.sqrt (b - a) := by
    simpa only [intervalIntegral.integral_of_le hab, μ] using hHolder
  have hI0 : 0 ≤ ∫ u in a..b, ‖f u‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hab
  have hmain := pow_le_pow_left₀ (norm_nonneg _) (hn.trans hcs) 2
  rw [mul_pow, Real.sq_sqrt hI0, Real.sq_sqrt (sub_nonneg.mpr hab)] at hmain
  simpa only [mul_comm] using hmain

end LeanLab.GoldbachAverage.WindowCauchy444
