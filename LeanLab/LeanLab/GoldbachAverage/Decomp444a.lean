import LeanLab.GoldbachAverage.Decomp402a
import LeanLab.ExceptionalSet.WindowParseval264
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Goldston and Yang, https://arxiv.org/abs/1601.06902v1 page 4 eq. 4.1.
The infinite moving window Fourier identity extends the proved finite interval formula.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444a
open MeasureTheory Set Filter FourierTransform
open Decomp287b

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

example : type_of% Decomp402a.moving_plancherel = type_of% moving_plancherel_proved := rfl

end LeanLab.GoldbachAverage.Decomp444a
