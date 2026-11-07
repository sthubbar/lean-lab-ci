import LeanLab.GoldbachAverage.MovingIntegrability402
import LeanLab.ExceptionalSet.TriangleKernel264
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
open scoped FourierTransform

section PlancherelHelpers

/-- The moving sum as a series of translated interval indicators, GY page 4 eq. 4.1. -/
private theorem movingSum_eq_indicator_tsum (a : ℕ → ℂ) (h x : ℝ) :
    movingSum a x h =
      ∑' n : ℕ, (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) x := by
  unfold movingSum
  apply tsum_congr
  intro n
  have hw : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔ x ∈ Ico ((n : ℝ) - h) n := by
    simp only [Set.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Ico ((n : ℝ) - h) n
  · rw [if_pos (hw.mpr hx), indicator_of_mem hx]
  · rw [if_neg (hw.not.mpr hx), indicator_of_notMem hx]

/-- Absolute summability makes the moving sum integrable: total mass at most `h` times the
coefficient mass.  Same majorant as `MovingIntegrability402.moving_square_integrable_proved`. -/
private theorem integrable_movingSum (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) : Integrable (fun x : ℝ => movingSum a x h) := by
  classical
  let u : ℕ → ℝ → ℝ := fun n => (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => ‖a n‖)
  let M : ℝ → ℝ := fun x => ∑' n, u n x
  have hu0 (n : ℕ) (x : ℝ) : 0 ≤ u n x := by
    simp only [u, Set.indicator_apply]
    split_ifs <;> positivity
  have hub (n : ℕ) (x : ℝ) : u n x ≤ ‖a n‖ := by
    simp only [u, Set.indicator_apply]
    split_ifs <;> simp
  have hus (x : ℝ) : Summable (fun n => u n x) :=
    Summable.of_nonneg_of_le (fun n => hu0 n x) (fun n => hub n x) ha
  have hum (n : ℕ) : Measurable (u n) := measurable_const.indicator measurableSet_Ico
  have hM : Measurable M := Measurable.tsum hum
  have hM0 (x : ℝ) : 0 ≤ M x := tsum_nonneg (fun n => hu0 n x)
  have hiM : Integrable M := by
    refine ⟨hM.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hM0)]
    have hconv (x : ℝ) : ENNReal.ofReal (M x) = ∑' n, ENNReal.ofReal (u n x) :=
      ENNReal.ofReal_tsum_of_nonneg (fun n => hu0 n x) (hus x)
    simp_rw [hconv]
    rw [lintegral_tsum (fun n => ((hum n).ennreal_ofReal).aemeasurable)]
    have hterm (n : ℕ) : (∫⁻ x : ℝ, ENNReal.ofReal (u n x)) =
        ENNReal.ofReal ‖a n‖ * ENNReal.ofReal h := by
      have he : (fun x => ENNReal.ofReal (u n x)) =
          (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => ENNReal.ofReal ‖a n‖) := by
        funext x
        simp only [u, Set.indicator_apply]
        split_ifs <;> simp_all
      rw [he, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
      congr 2
      ring
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (a n)) ha]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hn (x : ℝ) : ‖movingSum a x h‖ ≤ M x := by
    rw [movingSum_eq_indicator_tsum]
    have hsum : Summable (fun (n : ℕ) => ‖(Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) x‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun (n : ℕ) => ?_) ha
      simp only [Set.indicator_apply]
      split_ifs <;> simp
    calc ‖∑' n : ℕ, (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) x‖
        ≤ ∑' n : ℕ, ‖(Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) x‖ :=
          norm_tsum_le_tsum_norm hsum
      _ = M x := by
          apply tsum_congr
          intro n
          simp only [u, Set.indicator_apply]
          split_ifs <;> simp_all
  exact hiM.mono' (MovingIntegrability402.movingSum_measurable a h).aestronglyMeasurable
    (Eventually.of_forall hn)

/-- The character integrated over one window: `∫_b^c e(-αx) = (e(-αc) - e(-αb)) / (-2πiα)`. -/
private theorem integral_char_window (α : ℝ) (hα : α ≠ 0) (b c : ℝ) :
    ∫ x in b..c, Complex.exp (((-2 * Real.pi * α * x : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (((-2 * Real.pi * α * c : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-2 * Real.pi * α * b : ℝ) : ℂ) * Complex.I)) /
        (((-2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
  have hcR : (-2 * Real.pi * α : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα
  have hc : (((-2 * Real.pi * α : ℝ)) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hcR) Complex.I_ne_zero
  have hpt : ∀ x : ℝ, Complex.exp (((-2 * Real.pi * α * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((((-2 * Real.pi * α : ℝ)) : ℂ) * Complex.I) * (x : ℂ)) := by
    intro x
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  exact integral_exp_mul_complex hc

/-- The algebraic identity turning the window difference into the kernel times the `n`-th
character: `(e(-αn) - e(-α(n-h)))/(-2πiα) = e(-αn) (1 - e(αh))/(-2πiα)`. -/
private theorem window_kernel_algebra (α h : ℝ) (hα : α ≠ 0) (n : ℕ) :
    (Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-2 * Real.pi * α * ((n : ℝ) - h) : ℝ) : ℂ) * Complex.I)) /
        (((-2 * Real.pi * α : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
        ((1 - Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I)) /
          (-2 * Real.pi * α * Complex.I)) := by
  have hcR : (-2 * Real.pi * α : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα
  have hc : (((-2 * Real.pi * α : ℝ)) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hcR) Complex.I_ne_zero
  have hc2 : (-2 * Real.pi * α * Complex.I : ℂ) ≠ 0 := by
    rw [show (-2 * Real.pi * α * Complex.I : ℂ) = (((-2 * Real.pi * α : ℝ)) : ℂ) * Complex.I
      from by push_cast; ring]
    exact hc
  have e1 : Complex.exp (((-2 * Real.pi * α * ((n : ℝ) - h) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : (((-2 * Real.pi * α : ℝ)) : ℂ) * Complex.I = -2 * Real.pi * α * Complex.I := by
    push_cast
    ring
  rw [e1, e2]
  field_simp <;> ring

/-- GY page 4 eq. 4.1: the Fourier transform of the moving sum is the window kernel times
the coefficient series at `-α`. -/
private theorem fourier_movingSum_ne (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) {α : ℝ} (hα : α ≠ 0) :
    𝓕 (fun x : ℝ => movingSum a x h) α =
      ((1 - Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I)) /
        (-2 * Real.pi * α * Complex.I)) *
      ∑' n : ℕ, a n * Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  classical
  have hcont : Continuous fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp (by fun_prop)
  have hnormexp (v : ℝ) :
      ‖Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hFint (n : ℕ) : Integrable ((Ico ((n : ℝ) - h) (n : ℝ)).indicator
      (fun _ => a n)) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const (μ := volume) 1 measurableSet_Ico.nullMeasurableSet
      (a n) (Or.inr (by simp)))
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v) :=
    hcont.aestronglyMeasurable.mul
      (measurable_const.indicator measurableSet_Ico).aestronglyMeasurable
  have hint (n : ℕ) : Integrable (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v) := by
    refine Integrable.mono' (hFint n).norm (hmeas n) (Eventually.of_forall fun v => ?_)
    rw [norm_mul, hnormexp, one_mul]
  have hintval (n : ℕ) : (∫ v : ℝ, ‖Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
      (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v‖) = ‖a n‖ * h := by
    have he : (fun v : ℝ => ‖Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v‖) =
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => ‖a n‖) := by
      funext v
      rw [norm_mul, hnormexp, one_mul]
      by_cases hv : v ∈ Ico ((n : ℝ) - h) (n : ℝ)
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
        simp
    rw [he, integral_indicator_const ‖a n‖ measurableSet_Ico, measureReal_def, Real.volume_Ico,
      show (n : ℝ) - ((n : ℝ) - h) = h from by ring, ENNReal.toReal_ofReal hh.le,
      smul_eq_mul]
    ring
  have hsumint : Summable (fun n : ℕ => ∫ v : ℝ,
      ‖Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v‖) := by
    simpa only [hintval] using ha.mul_right h
  have hpt (v : ℝ) : (∑' n : ℕ, Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v) =
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) * movingSum a v h := by
    rw [movingSum_eq_indicator_tsum]
    exact (tsum_mul_left (f := fun n : ℕ =>
      (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v)
      (a := Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I)))
  have hswap := hasSum_integral_of_summable_integral_norm hint hsumint
  have hInt : (∫ v : ℝ, Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
      movingSum a v h) =
      ∑' n : ℕ, ∫ v : ℝ, Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v := by
    rw [show (∫ v : ℝ, Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        movingSum a v h) =
        ∫ v : ℝ, ∑' n : ℕ, Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
          (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v from by
      apply integral_congr_ae
      filter_upwards with v
      exact (hpt v).symm]
    exact hswap.tsum_eq.symm
  have hterm (n : ℕ) : (∫ v : ℝ,
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v) =
      Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
        ((1 - Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I)) /
          (-2 * Real.pi * α * Complex.I)) * a n := by
    have hsupp : (fun v : ℝ => Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) *
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun _ => a n) v) =
        (Ico ((n : ℝ) - h) (n : ℝ)).indicator (fun v =>
          Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) * a n) := by
      funext v
      by_cases hv : v ∈ Ico ((n : ℝ) - h) (n : ℝ)
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
        simp
    rw [hsupp, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (n : ℝ) - h ≤ (n : ℝ) by linarith),
      intervalIntegral.integral_mul_const, integral_char_window α hα,
      window_kernel_algebra α h hα n]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hexp' (v : ℝ) : Complex.exp ((↑(-2 * Real.pi * v * α) : ℂ) * Complex.I) =
      Complex.exp (((-2 * Real.pi * α * v : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  simp only [hexp', smul_eq_mul]
  rw [hInt]
  simp_rw [hterm]
  rw [show (fun n : ℕ => Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
        ((1 - Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I)) /
          (-2 * Real.pi * α * Complex.I)) * a n) =
      (fun n : ℕ => ((1 - Complex.exp ((2 * Real.pi * α * h : ℝ) * Complex.I)) /
          (-2 * Real.pi * α * Complex.I)) *
        (a n * Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)))
      from funext fun n => by ring]
  rw [tsum_mul_left]

/-- GY page 4 eq. 4.1: the modulus of the moving-sum transform is the sinc kernel times the
modulus of the coefficient series. -/
private theorem fourier_movingSum_norm_ne (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) {α : ℝ} (hα : α ≠ 0) :
    ‖𝓕 (fun x : ℝ => movingSum a x h) α‖ =
      h * |Real.sinc (Real.pi * h * α)| * ‖fourierSeries a (-α)‖ := by
  rw [fourier_movingSum_ne a ha h hh hα, norm_mul, LeanLab.ExceptionalSet.WindowParseval264.kernel_norm h α]
  have hser : ‖∑' n : ℕ,
      a n * Complex.exp (((-2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖
      = ‖fourierSeries a (-α)‖ := by
    congr 1
    rw [fourierSeries]
    apply tsum_congr
    intro n
    unfold eAdd
    congr 1
    push_cast
    ring
  rw [hser]
  have hsinc : h * |Real.sinc (Real.pi * h * α)| =
      |Real.sin (Real.pi * α * h)| / (Real.pi * |α|) := by
    have harg : Real.pi * h * α = Real.pi * α * h := by ring
    rw [harg]
    have hpa : Real.pi * α * h ≠ 0 :=
      mul_ne_zero (mul_ne_zero Real.pi_ne_zero hα) (ne_of_gt hh)
    have hαa : (0 : ℝ) < |α| := abs_pos.mpr hα
    rw [Real.sinc_of_ne_zero hpa, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos hh]
    field_simp
  rw [hsinc]

end PlancherelHelpers

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
  have hmem : MemLp (fun x : ℝ => movingSum a x h) 2 :=
    (memLp_two_iff_integrable_sq_norm (MovingIntegrability402.movingSum_measurable a h).aestronglyMeasurable).mpr
      hi
  have hI1 : Integrable (fun x : ℝ => movingSum a x h) := integrable_movingSum a ha h hh
  have hpl := LeanLab.ExceptionalSet.WindowParseval264.integral_norm_sq_fourier (fun x : ℝ => movingSum a x h) hI1 hmem
  have hFmem : MemLp (𝓕 (fun x : ℝ => movingSum a x h)) 2 :=
    LeanLab.ExceptionalSet.WindowParseval264.fourierIntegral_memLp (fun x : ℝ => movingSum a x h) hI1 hmem
  have hFsq : Integrable (fun α : ℝ => ‖𝓕 (fun x : ℝ => movingSum a x h) α‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).mp hFmem
  have hae : (fun α : ℝ => Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2)
      =ᵐ[volume] (fun α : ℝ => ‖𝓕 (fun x : ℝ => movingSum a x h) α‖ ^ 2 / h ^ 2) := by
    filter_upwards [show ∀ᵐ α : ℝ, α ≠ 0 from by rw [ae_iff]; simp] with α hα
    have hn := fourier_movingSum_norm_ne a ha h hh hα
    have hsq : (h * |Real.sinc (Real.pi * h * α)| * ‖fourierSeries a (-α)‖) ^ 2 / h ^ 2
        = Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, div_eq_iff (pow_ne_zero 2 (ne_of_gt hh))]
      ring
    rw [hn, hsq]
  have hIntH : Integrable (fun α : ℝ =>
      Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2) :=
    (hFsq.div_const (h ^ 2)).congr hae.symm
  have hneg : (fun α : ℝ => Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2) =
      fun α : ℝ => (fun β : ℝ => Real.sinc (Real.pi * h * β) ^ 2 *
        ‖fourierSeries a β‖ ^ 2) (-α) := by
    funext α
    show Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2
      = Real.sinc (Real.pi * h * -α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2
    rw [show Real.pi * h * -α = -(Real.pi * h * α) from by ring, Real.sinc_neg]
  have hIntG : Integrable (fun α : ℝ =>
      Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) := by
    rw [hneg] at hIntH
    simpa only [neg_neg] using hIntH.comp_neg
  refine ⟨hIntG, ?_⟩
  have hGH : (∫ α : ℝ, Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) =
      ∫ α : ℝ, Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2 := by
    rw [← integral_neg_eq_self (fun β : ℝ => Real.sinc (Real.pi * h * β) ^ 2 *
      ‖fourierSeries a β‖ ^ 2)]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    show Real.sinc (Real.pi * h * -α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2
      = Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2
    rw [show Real.pi * h * -α = -(Real.pi * h * α) from by ring, Real.sinc_neg]
  rw [hGH]
  calc (∫ α : ℝ, Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a (-α)‖ ^ 2)
      = ∫ α : ℝ, ‖𝓕 (fun x : ℝ => movingSum a x h) α‖ ^ 2 / h ^ 2 :=
        (integral_congr_ae hae.symm).symm
    _ = (∫ α : ℝ, ‖𝓕 (fun x : ℝ => movingSum a x h) α‖ ^ 2) / h ^ 2 := by
        simp only [div_eq_mul_inv, integral_mul_const]
    _ = (∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2 := by rw [hpl]


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
