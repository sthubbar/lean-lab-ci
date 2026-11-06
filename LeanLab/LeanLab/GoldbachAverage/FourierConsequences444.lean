import LeanLab.GoldbachAverage.Decomp444a
import LeanLab.GoldbachAverage.Decomp402d

/-!
Goldston and Suriajaya, https://arxiv.org/abs/2110.14250v2 page 9 eqs. 48 and 49.
The completed Fourier identity supplies the existing H and J reduction.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.FourierConsequences444
open MeasureTheory Set Filter
open Decomp287b Decomp402a GallagherReduction124 I2Bound124

/-- The exact continuous Gallagher target, GY page 4 eq. 4.2, from the new Fourier bridge. -/
theorem continuous_gallagher_proved (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2) ∧
      (∫ α in (0 : ℝ)..(1 / (2 * h)), ‖fourierSeries a α‖ ^ 2) ≤
        (Real.pi ^ 2 / 4) * ((∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2) := by
  have hi := moving_square_integrable a ha h hh
  refine ⟨hi, ?_⟩
  obtain ⟨hw, he⟩ := Decomp444a.moving_plancherel_proved a ha h hh hi
  have hc := (fourierSeries_continuous a ha).norm.pow 2
  have hsc : Continuous (fun α : ℝ =>
      Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) :=
    ((Real.continuous_sinc.comp (by fun_prop)).pow 2).mul hc
  have hb : (0 : ℝ) ≤ 1 / (2 * h) := by positivity
  have hpt (α : ℝ) (hα : α ∈ Icc 0 (1 / (2 * h))) :
      ‖fourierSeries a α‖ ^ 2 ≤ (Real.pi ^ 2 / 4) *
        (Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) := by
    have hs := mul_le_mul_of_nonneg_right (sinc_square_comparison hh hα)
      (sq_nonneg ‖fourierSeries a α‖)
    simpa only [one_mul, mul_assoc] using hs
  have hl := intervalIntegral.integral_mono_on hb
    (hc.intervalIntegrable (μ := volume) _ _) ((hsc.const_mul (Real.pi ^ 2 / 4)).intervalIntegrable (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_const_mul] at hl
  have hall := setIntegral_le_integral hw (Eventually.of_forall fun α =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)) (s := Ioc 0 (1 / (2 * h)))
  rw [← intervalIntegral.integral_of_le hb] at hall
  exact hl.trans (by rw [← he]; exact mul_le_mul_of_nonneg_left hall (by positivity))

example : type_of% Decomp287b.continuous_gallagher = type_of% continuous_gallagher_proved := rfl

/-- P0051 page 4 Theorem 2 eq. 19, proved on page 9 from Gallagher and the spatial split.
No Grosswald or BHMS zero variance input is used. -/
theorem gallagher_19_proved : GSInputs.GSGallagherVarianceBound := by
  apply gallagher_of_fourier
  refine ⟨Real.pi ^ 2 / 4, by positivity, ?_⟩
  intro N hN h hh hhN
  have hb := (continuous_gallagher_proved (coefficients N) (coefficients_summable N hN)
    h (by linarith)).2
  rw [Decomp402d.moving_mass_split_assembled N hN h hh hhN] at hb
  simpa only [fourierSeries_eq N hN, GSInputs.W] using hb

example : type_of% Decomp82.gallagher_19 = type_of% gallagher_19_proved := rfl

end LeanLab.GoldbachAverage.FourierConsequences444
