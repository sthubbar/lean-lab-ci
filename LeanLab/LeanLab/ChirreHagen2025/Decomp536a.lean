import Mathlib
import LeanLab.ChirreHagen2025.IntegralRepair391c

/-!
Partial summation components for the Mangoldt transfer.
Ramare 2013 pages 118 to 120, equation 5.1 and the following displays.
JRT 2023 page 3, proof of Lemma 9.
https://doi.org/10.4064/aa159-2-2
https://arxiv.org/abs/2303.13785
This file imports neither Decomp429e nor a module importing it.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp536a
open MeasureTheory Set Filter Topology

/-- Ramare page 119, phi two with a equal to log x divided by R. -/
noncomputable def tailWeight (a t : ℝ) : ℝ :=
  Real.exp (-a / Real.log t) / t ^ 2

/-- Ramare page 119, the derivative retained with its sign. -/
noncomputable def tailDerivative (a t : ℝ) : ℝ :=
  Real.exp (-a / Real.log t) * (a - 2 * Real.log t ^ 2) /
    (t ^ 3 * Real.log t ^ 2)

/-- Ramare page 119, differentiation before partial summation. -/
theorem tailWeight_hasDerivAt (a t : ℝ) (ht : 1 < t) :
    HasDerivAt (tailWeight a) (tailDerivative a t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith : 0 < t)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hlog := Real.hasDerivAt_log ht0
  have he := ((hasDerivAt_const t (-a)).div hlog hl0).exp
  have hh := he.div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
  convert hh using 1
  · funext u
    rfl
  · dsimp [tailDerivative]
    field_simp
    <;> ring

/-- Ramare page 119, phi two is nonnegative on its integration range. -/
theorem tailWeight_nonneg (a t : ℝ) : 0 ≤ tailWeight a t := by
  exact div_nonneg (Real.exp_pos _).le (sq_nonneg t)

/-- Ramare page 119, the elementary envelope used for the small branch. -/
theorem tailWeight_le_inverse_square (a t : ℝ) (ha : 0 ≤ a) (ht : 1 < t) :
    tailWeight a t ≤ 1 / t ^ 2 := by
  have he : Real.exp (-a / Real.log t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_pos ht).le)
  exact div_le_div_of_nonneg_right he (sq_nonneg t)

/-- Ramare page 119, one jump of a finite counting function. -/
theorem count_step_integral (T B v c : ℝ) (hTv : T < v) (hvB : v ≤ B)
    (f f' : ℝ → ℝ) (hd : ∀ t ∈ Icc T B, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc T B)) :
    (∫ t in Ioc T B, (Ici v).indicator (fun t => c * f' t) t) =
      c * (f B - f v) := by
  have hset : Ioc T B ∩ Ici v = Icc v B := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.2, ht.1.2⟩
    · intro ht
      exact ⟨⟨hTv.trans_le ht.1, ht.2⟩, ht.1⟩
  rw [setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hvB, intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hvB] at ht
    exact hd t ⟨hTv.le.trans ht.1, ht.2⟩
  · apply ContinuousOn.intervalIntegrable_of_Icc hvB
    exact hc.mono (fun t ht => ⟨hTv.le.trans ht.1, ht.2⟩)

/-- Ramare page 119, weighted finite zero counting on real ordinates. -/
noncomputable def finiteCount {ι : Type*} (s : Finset ι) (h c : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if h i ≤ t then c i else 0

/-- Ramare page 119, partial summation before the infinite zero limit. -/
theorem finite_partial_summation {ι : Type*} (s : Finset ι) (h c : ι → ℝ)
    (T B : ℝ) (hTB : T ≤ B) (hs : ∀ i ∈ s, h i ∈ Ioc T B)
    (f f' : ℝ → ℝ) (hd : ∀ t ∈ Icc T B, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc T B)) :
    (∑ i ∈ s, c i * f (h i)) = f B * (∑ i ∈ s, c i) -
      ∫ t in Ioc T B, finiteCount s h c t * f' t := by
  classical
  have hi : IntegrableOn f' (Ioc T B) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heq : (fun t => finiteCount s h c t * f' t) =
      fun t => ∑ i ∈ s, (Ici (h i)).indicator (fun t => c i * f' t) t := by
    funext t
    simp only [finiteCount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : h i ≤ t <;> simp [hh, indicator_of_mem, indicator_of_notMem]
  rw [heq, integral_finsetSum]
  · have hv : (∑ i ∈ s, ∫ t in Ioc T B,
          (Ici (h i)).indicator (fun t => c i * f' t) t) =
        ∑ i ∈ s, c i * (f B - f (h i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact count_step_integral T B (h i) (c i) (hs i hi).1 (hs i hi).2 f f' hd hc
    rw [hv]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    ring
  · intro i _
    exact (hi.const_mul (c i)).indicator measurableSet_Ici

/-- Ramare page 119, retain the absolute derivative through the saddle. -/
theorem tailDerivative_abs_bound (a T t : ℝ) (ha : 0 ≤ a) (hT : 1 < T) (ht : T ≤ t) :
    |tailDerivative a t| ≤ (a / Real.log T ^ 2 + 2) / t ^ 3 := by
  have ht1 : 1 < t := hT.trans_le ht
  have ht0 : 0 < t := by linarith
  have hLT : 0 < Real.log T := Real.log_pos hT
  have hLt : 0 < Real.log t := Real.log_pos ht1
  have hlogs : Real.log T ^ 2 ≤ Real.log t ^ 2 :=
    pow_le_pow_left₀ hLT.le (Real.log_le_log (by linarith) ht) 2
  have hr : a / Real.log t ^ 2 ≤ a / Real.log T ^ 2 :=
    div_le_div_of_nonneg_left ha (sq_pos_of_pos hLT) hlogs
  have habs : |a - 2 * Real.log t ^ 2| ≤ a + 2 * Real.log t ^ 2 := by
    calc
      _ = |a + -(2 * Real.log t ^ 2)| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-(2 * Real.log t ^ 2)| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ha, abs_neg, abs_of_nonneg (by positivity)]
  have he : Real.exp (-a / Real.log t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hLt.le)
  rw [tailDerivative, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : 0 < t ^ 3 * Real.log t ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < t ^ 3 * Real.log t ^ 2)).mpr
  have hm : Real.exp (-a / Real.log t) * |a - 2 * Real.log t ^ 2| ≤
      a + 2 * Real.log t ^ 2 := by
    calc
      _ ≤ 1 * |a - 2 * Real.log t ^ 2| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ _ := by simpa using habs
  apply hm.trans
  have hh : a ≤ (a / Real.log T ^ 2) * Real.log t ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hLt)).mp hr
  calc
    _ ≤ (a / Real.log T ^ 2 + 2) * Real.log t ^ 2 := by nlinarith
    _ = _ := by field_simp

/-- Ramare page 119, actual integrability of the signed derivative. -/
theorem tailDerivative_integrable (a T : ℝ) (ha : 0 ≤ a) (hT : 1 < T) :
    IntegrableOn (tailDerivative a) (Ioi T) := by
  have hT0 : 0 < T := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => (a / Real.log T ^ 2 + 2) / t ^ 3) (Ioi T) := by
    have hh := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT0).const_mul
      (a / Real.log T ^ 2 + 2)
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_neg (hT0.trans ht).le, Real.rpow_ofNat]
    ring
  have hc : ContinuousOn (tailDerivative a) (Ioi T) := by
    have hlog : ContinuousOn Real.log (Ioi T) :=
      continuousOn_id.log (fun t ht => ne_of_gt (hT0.trans ht))
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (-a / Real.log t)) (Ioi T) :=
      Real.continuous_exp.comp_continuousOn (continuousOn_const.div hlog
        (fun t ht => ne_of_gt (Real.log_pos (hT.trans ht))))
    exact (hexp.mul (continuousOn_const.sub ((hlog.pow 2).const_mul 2))).div
      ((continuousOn_id.pow 3).mul (hlog.pow 2))
      (fun t ht => mul_ne_zero (pow_ne_zero _ (ne_of_gt (hT0.trans ht)))
        (pow_ne_zero _ (ne_of_gt (Real.log_pos (hT.trans ht)))))
  apply hmaj.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using tailDerivative_abs_bound a T t ha hT ht.le

/-- Ramare page 119, the boundary weight vanishes at infinity. -/
theorem tailWeight_tendsto_zero (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (tailWeight a) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (tailWeight_nonneg a))
    (Filter.eventually_atTop.2 ⟨2, fun t ht => tailWeight_le_inverse_square a t ha (by linarith)⟩)
  have hh := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le]
  norm_num

/-- Ramare page 119, one jump integrated on the infinite tail. -/
theorem count_step_tail_integral (T v c : ℝ) (hTv : T < v)
    (f f' : ℝ → ℝ) (hd : ∀ t ∈ Ici T, HasDerivAt f (f' t) t)
    (hi : IntegrableOn f' (Ioi T)) (hz : Tendsto f atTop (𝓝 0)) :
    (∫ t in Ioi T, (Ici v).indicator (fun t => c * f' t) t) = -c * f v := by
  have hset : Ioi T ∩ Ici v = Ici v := by
    ext t
    exact ⟨fun h => h.2, fun h => ⟨hTv.trans_le h, h⟩⟩
  rw [setIntegral_indicator measurableSet_Ici, hset, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hd t (hTv.le.trans ht)) (hi.mono_set (Ioi_subset_Ioi hTv.le)) hz
  rw [hh]
  ring

/-- Ramare page 119, a countable real-ordinate counting function. -/
noncomputable def countSeries {ι : Type*} (h c : ι → ℝ) (t : ℝ) : ℝ :=
  ∑' i, if h i ≤ t then c i else 0

/-- Ramare page 119 first display, partial summation with an explicit
absolute-integral hypothesis for the exchange of sum and integral. -/
theorem infinite_partial_summation {ι : Type*} [Countable ι]
    (h c : ι → ℝ) (T : ℝ) (hT : ∀ i, T < h i)
    (f f' : ℝ → ℝ) (hd : ∀ t ∈ Ici T, HasDerivAt f (f' t) t)
    (hi : IntegrableOn f' (Ioi T)) (hz : Tendsto f atTop (𝓝 0))
    (habs : Summable (fun i => ∫ t in Ioi T,
      ‖(Ici (h i)).indicator (fun t => c i * f' t) t‖)) :
    HasSum (fun i => c i * f (h i))
      (-(∫ t in Ioi T, countSeries h c t * f' t)) := by
  have hfi (i : ι) : IntegrableOn
      ((Ici (h i)).indicator (fun t => c i * f' t)) (Ioi T) :=
    (hi.const_mul (c i)).indicator measurableSet_Ici
  have hh := (hasSum_integral_of_summable_integral_norm hfi habs).neg
  have heq : (fun i => -(∫ t in Ioi T,
      (Ici (h i)).indicator (fun t => c i * f' t) t)) =
      (fun i => c i * f (h i)) := by
    funext i
    rw [count_step_tail_integral T (h i) (c i) (hT i) f f' hd hi hz]
    ring
  rw [heq] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [countSeries, ← tsum_mul_right]
  apply tsum_congr
  intro i
  by_cases ht : h i ≤ t <;> simp [ht]

/-- Ramare page 119 second and third displays, the smooth counting main term. -/
noncomputable def smoothCount (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8

/-- Ramare page 119 third display, derivative of the smooth zero count. -/
theorem smoothCount_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt smoothCount (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hv : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht.ne' hpi
  have hd := (hasDerivAt_id t).div_const (2 * Real.pi)
  have hh := ((hd.mul (hd.log hv)).sub hd).add_const (7 / 8)
  convert hh using 1
  · funext u
    rfl
  · simp only [id_eq]
    field_simp [ht.ne', hpi]
    <;> ring

/-- Ramare page 119 second and third displays, signed discrepancy split.
All three integrals and the vanishing boundary are explicit premises. -/
theorem counting_error_identity (T N0 : ℝ) (N M M' f f' : ℝ → ℝ)
    (hM : ∀ t ∈ Ici T, HasDerivAt M (M' t) t)
    (hf : ∀ t ∈ Ici T, HasDerivAt f (f' t) t)
    (hiM : IntegrableOn (fun t => M' t * f t) (Ioi T))
    (hif : IntegrableOn (fun t => (M t - N0) * f' t) (Ioi T))
    (hiD : IntegrableOn (fun t => (N t - M t) * f' t) (Ioi T))
    (hlim : Tendsto (fun t => (M t - N0) * f t) atTop (𝓝 0)) :
    -(∫ t in Ioi T, (N t - N0) * f' t) =
      (M T - N0) * f T + (∫ t in Ioi T, M' t * f t) -
        ∫ t in Ioi T, (N t - M t) * f' t := by
  have hd (t : ℝ) (ht : t ∈ Ici T) :
      HasDerivAt (fun t => (M t - N0) * f t)
        (M' t * f t + (M t - N0) * f' t) t :=
    ((hM t ht).sub_const N0).mul (hf t ht)
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hiM.add hif) hlim
  rw [integral_add hiM hif, zero_sub] at hh
  have heq : (fun t => (N t - N0) * f' t) =
      fun t => (M t - N0) * f' t + (N t - M t) * f' t := by
    funext t
    ring
  rw [heq, integral_add hif hiD]
  linarith

/-- Ramare page 118, the exact critical-line magnitude before summation. -/
theorem critical_line_term_norm (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : z.re = 1 / 2) (m : ℕ) :
    ‖(m : ℂ) * (x : ℂ) ^ (z - 1) / (z * (z - 1))‖ =
      (m : ℝ) / (Real.sqrt x * ‖z * (z - 1)‖) := by
  rw [norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re, hz]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
    Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  ring

/-- LEAF. Ramare page 118 Lemma 4.3 and the first estimate after equation 5.1.
The source verifies the first zeros and uses Lemma 4.2 for their tail.
Zeros are counted with analytic multiplicity. This is a finite subsum
of the source reciprocal-mass bound 0.047, with no power of x. -/
theorem verified_reciprocal_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.047 := by
  sorry

/-- LEAF. Ramare page 118 paragraph after Lemma 4.3, citing Gourdon.
Every nontrivial zero through the verified height T0 is on the critical line.
This finite-height verification does not assume RH at other heights. -/
theorem verified_low_zeros (z : ℂ)
    (hz : riemannZeta z = 0) (hz0 : 0 < z.re) (hz1 : z.re < 1)
    (hT : |z.im| ≤ 2.44 * 10 ^ 12) : z.re = 1 / 2 := by
  sorry

/-- Ramare page 118, the verified low-zero contribution to equation 5.1.
CONDITIONAL ON the reciprocal-mass certificate and finite-height verification. -/
theorem low_zero_sum_bound (x : ℝ) (hx : 0 < x) (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧
      |z.im| ≤ 2.44 * 10 ^ 12) :
    ‖∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℂ) *
      (x : ℂ) ^ (z - 1) / (z * (z - 1))‖ ≤ 0.047 / Real.sqrt x := by
  have hr (z : ℂ) (hz : z ∈ s) : z.re = 1 / 2 :=
    verified_low_zeros z (hs z hz).1 (hs z hz).2.1 (hs z hz).2.2.1 (hs z hz).2.2.2
  calc
    _ ≤ ∑ z ∈ s, ‖(analyticOrderNatAt riemannZeta z : ℂ) *
        (x : ℂ) ^ (z - 1) / (z * (z - 1))‖ := norm_sum_le _ _
    _ = (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) /
        Real.sqrt x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      rw [critical_line_term_norm x hx z (hr z hz)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (verified_reciprocal_mass s
      (fun z hz => ⟨(hs z hz).1, (hs z hz).2.1, (hs z hz).2.2.1⟩)) (Real.sqrt_nonneg _)

/-- Ramare page 118, imaginary parts dominate the zero denominator. -/
theorem denominator_im_sq (z : ℂ) : z.im ^ 2 ≤ ‖z * (z - 1)‖ := by
  have h1 := Complex.abs_im_le_norm z
  have h2 := Complex.abs_im_le_norm (z - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at h2
  rw [norm_mul, ← sq_abs z.im, pow_two]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- Ramare page 118, the paired zero numerator after reflection. -/
theorem paired_numerator_bound (x φ : ℝ) (hx : 1 ≤ x) (z : ℂ)
    (hlo : φ ≤ z.re) (hhi : z.re ≤ 1 - φ) :
    ‖(x : ℂ) ^ (z - 1) + (x : ℂ) ^ (-z)‖ ≤
      1 / Real.sqrt x + x ^ (-φ) := by
  have hx0 : 0 < x := by linarith
  have hhalf : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  apply (norm_add_le _ _).trans
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re]
  by_cases hh : z.re ≤ 1 / 2
  · have h1 := Real.rpow_le_rpow_of_exponent_le hx (show z.re - 1 ≤ -(1 / 2) by linarith)
    have h2 := Real.rpow_le_rpow_of_exponent_le hx (show -z.re ≤ -φ by linarith)
    rw [hhalf] at h1
    linarith
  · have h1 := Real.rpow_le_rpow_of_exponent_le hx (show z.re - 1 ≤ -φ by linarith)
    have h2 := Real.rpow_le_rpow_of_exponent_le hx (show -z.re ≤ -(1 / 2) by linarith)
    rw [hhalf] at h2
    linarith

/-- Ramare page 119 first display, specialized to the actual zero-tail weight.
The sum-integral exchange retains its absolute-integral premise. -/
theorem tail_partial_summation {ι : Type*} [Countable ι]
    (h c : ι → ℝ) (a T : ℝ) (ha : 0 ≤ a) (hT : 1 < T) (hh : ∀ i, T < h i)
    (habs : Summable (fun i => ∫ t in Ioi T,
      ‖(Ici (h i)).indicator (fun t => c i * tailDerivative a t) t‖)) :
    HasSum (fun i => c i * tailWeight a (h i))
      (-(∫ t in Ioi T, countSeries h c t * tailDerivative a t)) := by
  exact infinite_partial_summation h c T hh (tailWeight a) (tailDerivative a)
    (fun t ht => tailWeight_hasDerivAt a t (hT.trans_le ht))
    (tailDerivative_integrable a T ha hT) (tailWeight_tendsto_zero a ha) habs
/-- Ramare page 118 first bound after equation 5.1, a paired high-zero term. -/
theorem paired_term_bound (x φ : ℝ) (hx : 1 ≤ x) (z : ℂ) (hzi : z.im ≠ 0)
    (hlo : φ ≤ z.re) (hhi : z.re ≤ 1 - φ) (m : ℕ) :
    ‖(m : ℂ) * ((x : ℂ) ^ (z - 1) + (x : ℂ) ^ (-z)) / (z * (z - 1))‖ ≤
      (m : ℝ) / (Real.sqrt x * ‖z * (z - 1)‖) +
        (m : ℝ) * x ^ (-φ) / z.im ^ 2 := by
  have hD := denominator_im_sq z
  have hi2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hzi
  rw [norm_div, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ) * (1 / Real.sqrt x + x ^ (-φ)) / ‖z * (z - 1)‖ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (paired_numerator_bound x φ hx z hlo hhi)
          (Nat.cast_nonneg m)) (norm_nonneg _)
    _ = (m : ℝ) / (Real.sqrt x * ‖z * (z - 1)‖) +
        (m : ℝ) * x ^ (-φ) / ‖z * (z - 1)‖ := by ring
    _ ≤ _ := add_le_add le_rfl
      (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg m)
        (Real.rpow_nonneg (by linarith : 0 ≤ x) _)) hi2 hD)

/-- Ramare page 119, conversion from the zero-free power to phi two. -/
theorem zero_free_weight_identity (x R t : ℝ) (hx : 0 < x) :
    x ^ (-(1 / (R * Real.log t))) / t ^ 2 = tailWeight (Real.log x / R) t := by
  have he : Real.log x * (-(1 / (R * Real.log t))) =
      -(Real.log x / R) / Real.log t := by ring
  rw [Real.rpow_def_of_pos hx, he]
  rfl

/-- Ramare page 119, the auxiliary integral before the logarithmic substitution. -/
noncomputable def auxiliaryKernel (a t : ℝ) : ℝ :=
  tailWeight a t * Real.log t / (2 * Real.pi)

/-- Ramare page 119 definition of I, the exact logarithmic Jacobian. -/
theorem auxiliary_log_jacobian (a t : ℝ) (ht : 0 < t) :
    t⁻¹ * (Real.log t * Real.exp (-a / Real.log t - Real.log t) / (2 * Real.pi)) =
      auxiliaryKernel a t := by
  rw [Real.exp_sub, Real.exp_log ht]
  dsimp [auxiliaryKernel, tailWeight]
  ring

/-- Ramare page 119 definition of I, substitution u equal to log t. -/
theorem auxiliary_log_substitution (a T : ℝ) (hT : 0 < T) :
    (∫ t in Ioi T, auxiliaryKernel a t) =
      ∫ u in Ioi (Real.log T), u * Real.exp (-a / u - u) / (2 * Real.pi) := by
  rw [← integral_comp_log_Ioi _ hT]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (auxiliary_log_jacobian a t (hT.trans ht)).symm

/-- Ramare page 119 definition of I, actual integrability before substitution.
The existing scalar repair supplies integrability in the logarithmic variable. -/
theorem auxiliaryKernel_integrable (a T : ℝ) (ha : 0 ≤ a) (hT : 1 < T) :
    IntegrableOn (auxiliaryKernel a) (Ioi T) := by
  have hT0 : 0 < T := by linarith
  have hh := (integrableOn_comp_log_Ioi
    (fun u : ℝ => u * Real.exp (-a / u - u) / (2 * Real.pi)) hT0).2
    (IntegralRepair391c.auxiliary_integral_bound a (Real.log T) ha (Real.log_pos hT)).1
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [smul_eq_mul] using auxiliary_log_jacobian a t (hT0.trans ht)
/-- Ramare page 118 last display, a coarse logarithm bound for T0 over two pi. -/
theorem cutoff_ratio_log_le :
    Real.log ((2.44 * 10 ^ 12 : ℝ) / (2 * Real.pi)) ≤ 26.7 := by
  have hpi : (3.14 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hp : 0 < 2 * Real.pi := by positivity
  rw [Real.log_le_iff_le_exp (by positivity)]
  have he26 : (2.718 : ℝ) ^ 26 ≤ Real.exp 26 := by
    calc
      _ ≤ Real.exp 1 ^ 26 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = Real.exp 26 := by rw [← Real.exp_nat_mul]; norm_num
  have he7 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.7) 4
  norm_num [Finset.sum_range_succ] at he7
  have he : (2.718 : ℝ) ^ 26 * (12013 / 6000) ≤ Real.exp 26.7 := by
    calc
      _ ≤ Real.exp 26 * Real.exp 0.7 := by
        exact mul_le_mul he26 (by linarith) (by norm_num) (Real.exp_pos _).le
      _ = Real.exp 26.7 := by rw [← Real.exp_add]; norm_num
  apply le_trans _ he
  apply (div_le_iff₀ hp).mpr
  nlinarith

/-- Ramare page 118 last display, the printed small-tail rounding. -/
theorem small_tail_numeric :
    Real.log ((2.44 * 10 ^ 12 : ℝ) / (2 * Real.pi)) /
      (2 * Real.pi * (2.44 * 10 ^ 12)) *
      (1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12)) ≤ 1.75 / 10 ^ 12 := by
  have hpi : (3.14 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hp : 0 < 2 * Real.pi := by positivity
  have hbound : 1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12) ≤ (1.000000001 : ℝ) := by
    linarith [Real.pi_lt_four]
  have hh := mul_le_mul_of_nonneg_right cutoff_ratio_log_le
    (show 0 ≤ (1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12)) / (2 * Real.pi * (2.44 * 10 ^ 12)) by positivity)
  have hrat : Real.log ((2.44 * 10 ^ 12 : ℝ) / (2 * Real.pi)) /
      (2 * Real.pi * (2.44 * 10 ^ 12)) *
      (1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12)) ≤
      26.7 * (1.000000001 : ℝ) / (2 * Real.pi * (2.44 * 10 ^ 12)) := by
    calc
      _ = Real.log ((2.44 * 10 ^ 12 : ℝ) / (2 * Real.pi)) *
          ((1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12)) / (2 * Real.pi * (2.44 * 10 ^ 12))) := by ring
      _ ≤ 26.7 * ((1 + 1.36 * (2 * Real.pi) / (2.44 * 10 ^ 12)) / (2 * Real.pi * (2.44 * 10 ^ 12))) := hh
      _ ≤ _ := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 26.7))
          (show 0 ≤ 2 * Real.pi * (2.44 * 10 ^ 12) by positivity)
  apply hrat.trans
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * (2.44 * 10 ^ 12))).mpr
  nlinarith
/-- Ramare page 119, the smooth counting term has no boundary at infinity. -/
theorem smoothCount_tail_boundary (a N0 : ℝ) :
    Tendsto (fun t => (smoothCount t - N0) * tailWeight a t) atTop (𝓝 0) := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hb0 := ((hlog.div_const (2 * Real.pi)).sub
    (hinv.const_mul ((Real.log (2 * Real.pi) + 1) / (2 * Real.pi)))).add
      ((hinv.pow 2).const_mul (7 / 8 - N0))
  have hb : Tendsto (fun t => (smoothCount t - N0) / t ^ 2) atTop (𝓝 0) := by
    convert hb0.congr' ?_ using 1 <;> try norm_num
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp [smoothCount]
    rw [Real.log_div ht.ne' hpi]
    field_simp
    <;> ring
  have he0 : Tendsto (fun t : ℝ => -a / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh := ((Real.continuous_exp.tendsto 0).comp he0).mul hb
  convert hh using 1
  · funext t
    dsimp [tailWeight]
    ring
  · simp
end LeanLab.ChirreHagen2025.Decomp536a
