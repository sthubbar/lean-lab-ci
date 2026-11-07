import LeanLab.GoldbachAverage.MovingIntegrability402
import LeanLab.ExceptionalSet.WindowParseval264
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Goldston and Yang, arXiv 1601.06902v1 page 4 eqs. 4.1 and 4.2.
This splits the continuous Gallagher leaf into spatial integrability and Plancherel.
The sinc comparison and the exact target assembly are proved separately.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402a
open MeasureTheory Set Filter FourierTransform
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

/-- GY page 4 before eq. 4.1, absolute summability gives an integrable moving sum.
Tonelli bounds its norm by the sum of translated coefficient norms. -/
theorem movingSum_integrable (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => movingSum a x h) := by
  classical
  let u : ℕ → ℝ → ℝ := fun n => (Ico ((n : ℝ) - h) n).indicator (fun _ => ‖a n‖)
  let v : ℕ → ℝ → ℂ := fun n => (Ico ((n : ℝ) - h) n).indicator (fun _ => a n)
  let M : ℝ → ℝ := fun x => ∑' n, u n x
  let A : ℝ := ∑' n, ‖a n‖
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
  have hMA (x : ℝ) : M x ≤ A := (hus x).tsum_le_tsum (fun n => hub n x) ha
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
          (Ico ((n : ℝ) - h) n).indicator (fun _ => ENNReal.ofReal ‖a n‖) := by
        funext x
        simp only [u, Set.indicator_apply]
        split_ifs <;> simp_all
      rw [he, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
      congr 2
      ring
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (a n)) ha]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hvnorm (n : ℕ) (x : ℝ) : ‖v n x‖ = u n x := by
    simp only [u, v, Set.indicator_apply]
    split_ifs <;> simp_all
  have hvm (n : ℕ) : Measurable (v n) := measurable_const.indicator measurableSet_Ico
  have hv : Measurable (fun x => ∑' n, v n x) := Measurable.tsum hvm
  have heq (x : ℝ) : movingSum a x h = ∑' n, v n x := by
    apply tsum_congr
    intro n
    have hw : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔
        x ∈ Ico ((n : ℝ) - h) n := by
      simp only [Set.mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    dsimp only [v]
    by_cases hx : x ∈ Ico ((n : ℝ) - h) n
    · rw [if_pos (hw.mpr hx), indicator_of_mem hx]
    · rw [if_neg (hw.not.mpr hx), indicator_of_notMem hx]
  have hms : Measurable (movingSum a · h) := by
    convert hv using 1
    funext x
    exact heq x
  have hn (x : ℝ) : ‖movingSum a x h‖ ≤ M x := by
    rw [heq]
    have hs : Summable (fun n => ‖v n x‖) := by simpa only [hvnorm] using hus x
    simpa only [hvnorm] using norm_tsum_le_tsum_norm hs
  exact hiM.mono' hms.aestronglyMeasurable (Eventually.of_forall hn)

/-- GY page 4 definition of C, written as a series of translated interval indicators. -/
theorem movingSum_eq_indicators (a : ℕ → ℂ) (h x : ℝ) :
    movingSum a x h = ∑' n : ℕ,
      (Ico ((n : ℝ) - h) n).indicator (fun _ : ℝ => a n) x := by
  apply tsum_congr
  intro n
  have hw : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔ x ∈ Ico ((n : ℝ) - h) n := by
    simp only [mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Ico ((n : ℝ) - h) n
  · rw [if_pos (hw.mpr hx), indicator_of_mem hx]
  · rw [if_neg (hw.not.mpr hx), indicator_of_notMem hx]

/-- GY page 4 eq. 4.1, one coefficient has L1 mass h times its absolute value. -/
theorem indicator_norm_integral (n : ℕ) (z : ℂ) (h : ℝ) (hh : 0 ≤ h) :
    (∫ x : ℝ, ‖(Ico ((n : ℝ) - h) n).indicator (fun _ : ℝ => z) x‖) = h * ‖z‖ := by
  simp_rw [norm_indicator_eq_indicator_norm]
  rw [integral_indicator measurableSet_Ico]
  simp [measureReal_def, Real.volume_Ico, hh, mul_comm]

/-- LEAF. GY page 4 eq. 4.1, termwise Fourier integration of the moving window.
The interval transform is elementary. Absolute coefficient summability justifies the interchange.
This leaf contains no Plancherel or square integral assertion. -/
theorem movingSum_fourier (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) (t : ℝ) (ht : t ≠ 0) :
    𝓕 (fun x : ℝ => movingSum a x h) t =
      ((1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)) * fourierSeries a (-t) := by
  classical
  let v : ℕ → ℝ → ℂ := fun n =>
    (Ico ((n : ℝ) - h) n).indicator (fun _ : ℝ => a n)
  let E : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)
  let F : ℕ → ℝ → ℂ := fun n x => E x * v n x
  have hE (x : ℝ) : ‖E x‖ = 1 := by
    simp [E, Complex.norm_exp]
  have hv (n : ℕ) : Integrable (v n) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ico.nullMeasurableSet
      (a n) (Or.inr (by simp)))
  have hFn (n : ℕ) (x : ℝ) : ‖F n x‖ = ‖v n x‖ := by
    simp only [F, norm_mul, hE, one_mul]
  have hF (n : ℕ) : Integrable (F n) := by
    apply (hv n).norm.mono'
    · exact ((by fun_prop : Continuous E).measurable.mul
        (measurable_const.indicator measurableSet_Ico)).aestronglyMeasurable
    · exact Eventually.of_forall (fun x => (hFn n x).le)
  have hmass (n : ℕ) : (∫ x : ℝ, ‖F n x‖) = h * ‖a n‖ := by
    simp_rw [hFn]
    exact indicator_norm_integral n (a n) h hh.le
  have hsum : Summable (fun n => ∫ x : ℝ, ‖F n x‖) := by
    simp_rw [hmass]
    exact ha.mul_left h
  have hinter : 𝓕 (fun x : ℝ => movingSum a x h) t =
      ∑' n : ℕ, 𝓕 (v n) t := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    change (∫ x : ℝ, E x * movingSum a x h) = ∑' n : ℕ, ∫ x : ℝ, F n x
    simp_rw [movingSum_eq_indicators, ← tsum_mul_left]
    exact (integral_tsum_of_summable_integral_norm hF hsum).symm
  have hterm (n : ℕ) : 𝓕 (v n) t =
      ((1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)) * (a n * eAdd (-t * n)) := by
    have hw := LeanLab.ExceptionalSet.WindowParseval264.fourier_window
      {(n : ℤ)} (fun _ => a n) hh.le ht
    have he : LeanLab.ExceptionalSet.WindowParseval264.window {(n : ℤ)} (fun _ => a n) h =
        v n := by
      funext x
      simp [LeanLab.ExceptionalSet.WindowParseval264.window, v]
    rw [he] at hw
    simp only [Finset.sum_singleton, Int.cast_natCast] at hw
    have hp : Complex.exp ((-2 * Real.pi * t * Complex.I) * (n : ℝ)) = eAdd (-t * n) := by
      unfold eAdd
      congr 1
      push_cast
      ring
    rw [hp] at hw
    exact hw
  rw [hinter]
  simp_rw [hterm]
  rw [tsum_mul_left]
  rfl

/-- GY page 4 eq. 4.1, integral Plancherel reused from the proved lab bridge. -/
theorem movingSum_parseval (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) :
    Integrable (fun t : ℝ => ‖𝓕 (fun x : ℝ => movingSum a x h) t‖ ^ 2) ∧
    (∫ t : ℝ, ‖𝓕 (fun x : ℝ => movingSum a x h) t‖ ^ 2) =
      ∫ x : ℝ, ‖movingSum a x h‖ ^ 2 := by
  have h1 := movingSum_integrable a ha h hh
  have h2 := MovingIntegrability402.movingSum_memLp a ha h hh
  have hf := LeanLab.ExceptionalSet.WindowParseval264.fourierIntegral_memLp _ h1 h2
  exact ⟨(memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf,
    LeanLab.ExceptionalSet.WindowParseval264.integral_norm_sq_fourier _ h1 h2⟩

/-- GY page 4 eq. 4.1, the square of the interval kernel is h squared times sinc squared. -/
theorem kernel_sinc_square (h t : ℝ) (ht : t ≠ 0) :
    ‖(1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
      (-2 * Real.pi * t * Complex.I)‖ ^ 2 = h ^ 2 * Real.sinc (Real.pi * t * h) ^ 2 := by
  rw [LeanLab.ExceptionalSet.WindowParseval264.kernel_norm]
  by_cases hh : h = 0
  · simp [hh]
  rw [Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero Real.pi_ne_zero ht) hh),
    div_pow, sq_abs, mul_pow, sq_abs]
  field_simp
  <;> ring

/-- The exact moving_plancherel target from GY page 4 eq. 4.1.
The Fourier evaluation and the already proved lab Plancherel theorem are independent steps. -/
theorem moving_plancherel_proved (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h)
    (hi : Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2)) :
    Integrable (fun α : ℝ => Real.sinc (Real.pi * h * α) ^ 2 *
      ‖fourierSeries a α‖ ^ 2) ∧
    (∫ α : ℝ, Real.sinc (Real.pi * h * α) ^ 2 * ‖fourierSeries a α‖ ^ 2) =
      (∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2 := by
  obtain ⟨hF, he⟩ := movingSum_parseval a ha h hh
  have heval : (fun t : ℝ => ‖𝓕 (fun x : ℝ => movingSum a x h) (-t)‖ ^ 2 / h ^ 2) =ᵐ[volume]
      (fun t : ℝ => Real.sinc (Real.pi * h * t) ^ 2 * ‖fourierSeries a t‖ ^ 2) := by
    have hn : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hn] with t ht
    rw [movingSum_fourier a ha h hh (-t) (neg_ne_zero.mpr ht), norm_mul, mul_pow,
      kernel_sinc_square h (-t) (neg_ne_zero.mpr ht), neg_neg]
    have hs : Real.pi * (-t) * h = -(Real.pi * h * t) := by ring
    rw [hs, Real.sinc_neg]
    field_simp
  refine ⟨(hF.comp_neg.div_const (h ^ 2)).congr heval, ?_⟩
  rw [← integral_congr_ae heval, integral_div]
  have href := integral_neg_eq_self (fun t : ℝ => ‖𝓕 (fun x : ℝ => movingSum a x h) t‖ ^ 2)
  rw [href, he]

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
  exact moving_plancherel_proved a ha h hh hi

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
