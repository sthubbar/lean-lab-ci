import LeanLab.GoldbachAverage.MovingIntegrability402
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Goldston and Yang, arXiv 1601.06902v1 page 4 eqs. 4.1 and 4.2.
This splits the continuous Gallagher leaf into spatial integrability and Plancherel.
The sinc comparison and the exact target assembly are proved separately.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402a
open MeasureTheory Set Filter
open Decomp287b

/-- The coefficient series in GY page 4 Section 4 is continuous by uniform convergence. -/
theorem fourierSeries_continuous (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) : Continuous (fourierSeries a) := by
  change Continuous (fun α : ℝ => ∑' n : ℕ, a n * eAdd (α * n))
  apply continuous_tsum (fun n : ℕ => (continuous_const : Continuous (fun _ : ℝ => a n)).mul (continuous_eAdd_mul (n : ℝ))) ha
  intro n α
  change ‖a n * eAdd (α * (n : ℝ))‖ ≤ ‖a n‖
  simp only [norm_mul, norm_eAdd, mul_one, le_refl]

/-- GY page 4 before eq. 4.2, the sinc lower bound on the positive half window. -/
theorem sinc_lower {u : ℝ} (hu : 0 ≤ u) (huπ : u ≤ Real.pi / 2) :
    2 / Real.pi ≤ Real.sinc u := by
  by_cases hu0 : u = 0
  · subst u
    rw [Real.sinc_zero]
    exact (div_le_one Real.pi_pos).mpr Real.two_le_pi
  · rw [Real.sinc_of_ne_zero hu0, le_div_iff₀ (lt_of_le_of_ne hu (Ne.symm hu0))]
    exact Real.mul_le_sin hu huπ

/-- GY page 4 before eq. 4.2, the squared reciprocal sinc comparison. -/
theorem sinc_square_comparison {h α : ℝ} (hh : 0 < h)
    (hα : α ∈ Icc 0 (1 / (2 * h))) :
    1 ≤ (Real.pi ^ 2 / 4) * Real.sinc (Real.pi * h * α) ^ 2 := by
  have ha0 : 0 ≤ α := hα.1
  have hu : 0 ≤ Real.pi * h * α := by positivity
  have hup : Real.pi * h * α ≤ Real.pi / 2 := by
    have ht := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * h)).mp hα.2
    nlinarith [Real.pi_pos]
  have hl := sinc_lower hu hup
  have hr : 0 ≤ 2 / Real.pi := by positivity
  have hs := pow_le_pow_left₀ hr hl 2
  have he : (Real.pi ^ 2 / 4) * (2 / Real.pi) ^ 2 = 1 := by
    field_simp
    norm_num
  have hc := mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.pi ^ 2 / 4 by positivity)
  rw [he] at hc
  exact hc

/-- LEAF. GY page 4 eq. 4.1, spatial integrability of the moving coefficient square.
Absolute summability gives a finite square integral for every fixed positive width.
This assertion contains no Fourier comparison. -/
theorem moving_square_integrable (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2) := by
  exact MovingIntegrability402.moving_square_integrable_proved a ha h hh

/-- LEAF. GY page 4 eq. 4.1 and page 5 eq. 4.3, the Plancherel identity.
Translate the centered window by half its width and multiply by h squared.
The sinc weighted Fourier square is integrable. Endpoint choices agree almost everywhere.
The spatial integrability premise is explicit so this leaf only supplies the transform step. -/
theorem moving_plancherel (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h)
    (hi : Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2)) :
    Integrable (fun α : ℝ => Real.sinc (Real.pi * h * α) ^ 2 *
      ‖fourierSeries a α‖ ^ 2) ∧
    (∫ α : ℝ, Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) =
      (∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2 := by
  sorry

/-- The exact continuous_gallagher target follows from the two smaller leaves.
CONDITIONAL ON moving_plancherel. -/
theorem continuous_gallagher_assembled (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2) ∧
      (∫ α in (0 : ℝ)..(1 / (2 * h)), ‖fourierSeries a α‖ ^ 2) ≤
        (Real.pi ^ 2 / 4) * ((∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2) := by
  have hi := moving_square_integrable a ha h hh
  refine ⟨hi, ?_⟩
  obtain ⟨hw, he⟩ := moving_plancherel a ha h hh hi
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

example : type_of% continuous_gallagher = type_of% continuous_gallagher_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402a
