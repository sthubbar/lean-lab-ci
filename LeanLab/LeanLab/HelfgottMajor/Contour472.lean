import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
An elementary square energy budget for the left contour of P0014 page 35.
The pointwise logarithmic derivative estimate is a separate analytic input.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Contour472
open Real MeasureTheory Set Filter
open scoped Topology

/-- The primitive for the logarithmic square tail used to bound display 4.13.
Derived calculus for P0014 page 35. The parameter a is any real constant.
-/
theorem log_square_tail_derivative (a t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => -((log x + a) ^ 2 + 2 * (log x + a) + 2) / x)
      ((log t + a) ^ 2 / t ^ 2) t := by
  convert (((((hasDerivAt_log ht).add_const a).pow 2).add
    (((hasDerivAt_log ht).add_const a).const_mul 2)).add_const 2).neg.div
      (hasDerivAt_id t) ht using 1
  · ext x
    simp only [Pi.div_apply, Pi.neg_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  · dsimp
    field_simp
    ring

/-- The logarithmic square tail primitive tends to zero at infinity.
Derived convergence step for P0014 page 35, display 4.13.
-/
theorem log_square_tail_primitive_tendsto (a : ℝ) :
    Tendsto (fun x : ℝ => -((log x + a) ^ 2 + 2 * (log x + a) + 2) / x)
      atTop (𝓝 0) := by
  have h2 := tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 := tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  simp only [one_mul, add_zero, pow_one, pow_zero] at h2 h1 h0
  convert ((h2.add (h1.const_mul (2 * a + 2))).add
    (h0.const_mul (a ^ 2 + 2 * a + 2))).neg using 1
  · ext x
    ring
  · simp

/-- The logarithmic square tail is integrable and has its exact elementary value.
Derived tail budget for P0014 page 35, display 4.13.
-/
theorem log_square_tail_integral (a b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (log t + a) ^ 2 / t ^ 2) (Ioi b) ∧
      (∫ t : ℝ in Ioi b, (log t + a) ^ 2 / t ^ 2) =
        ((log b + a) ^ 2 + 2 * (log b + a) + 2) / b := by
  have hd : ∀ t ∈ Ici b,
      HasDerivAt (fun x : ℝ => -((log x + a) ^ 2 + 2 * (log x + a) + 2) / x)
        ((log t + a) ^ 2 / t ^ 2) t := by
    intro t ht
    exact log_square_tail_derivative a t (ne_of_gt (hb.trans_le ht))
  have hn : ∀ t ∈ Ioi b, 0 ≤ (log t + a) ^ 2 / t ^ 2 := by
    intro t ht
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn
    (log_square_tail_primitive_tendsto a), ?_⟩
  simpa only [zero_sub, neg_div, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hn (log_square_tail_primitive_tendsto a)

/-- A coarse exact tail budget with ample room for the contour coefficient 6.01.
Derived scalar bound for P0014 page 35, display 4.13.
-/
theorem log_square_tail_four_le :
    (∫ t : ℝ in Ioi 4, (log t + 4) ^ 2 / t ^ 2) ≤ 25 / 2 := by
  rw [(log_square_tail_integral 4 4 (by norm_num)).2]
  have h0 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have h1 : log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only [Nat.cast_ofNat]
    linarith
  nlinarith

/-- The exact Cauchy kernel mass on the left contour.
Source P0014 page 35, the factor one over one quarter plus the height squared.
-/
theorem cauchy_kernel_integral :
    Integrable (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) ∧
      (∫ t : ℝ, (1 / 4 + t ^ 2)⁻¹) = 2 * π := by
  have heq : (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) =
      fun t : ℝ => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    ext t
    have h1 : (1 / 4 + t ^ 2) ≠ 0 := by positivity
    have h2 : (1 + (2 * t) ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  refine ⟨(integrable_inv_one_add_mul_sq (by norm_num : (2 : ℝ) ≠ 0)).const_mul 4, ?_⟩
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq]
  norm_num
  ring

/-- A scalar logarithmic envelope has a square energy below the contour budget.
CONDITIONAL ON the two pointwise envelope bounds.
Derived estimate for P0014 page 35, display 4.13, using a split at height four.
-/
theorem scalar_contour_energy (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (h0 : ∀ t : ℝ, 0 ≤ f t)
    (hsmall : ∀ t : ℝ, |t| ≤ 4 → f t ≤ 5)
    (hlarge : ∀ t : ℝ, 4 < |t| → f t ≤ log |t| + 4) :
    Integrable (fun t : ℝ => f t ^ 2 / (1 / 4 + t ^ 2)) ∧
      (∫ t : ℝ, f t ^ 2 / (1 / 4 + t ^ 2)) ≤ 50 * π + 25 := by
  let P : ℝ → ℝ := (Ioi 4).indicator (fun t : ℝ => (log t + 4) ^ 2 / t ^ 2)
  have hP : Integrable P :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (log_square_tail_integral 4 4 (by norm_num)).1
  have hN : Integrable (fun t : ℝ => P (-t)) := hP.comp_neg
  have hPn (t : ℝ) : 0 ≤ P t := by
    dsimp [P]
    exact indicator_nonneg (fun _ _ => by positivity) t
  have hPi : (∫ t : ℝ, P t) ≤ 25 / 2 := by
    simpa only [P, integral_indicator measurableSet_Ioi] using log_square_tail_four_le
  have hNi : (∫ t : ℝ, P (-t)) ≤ 25 / 2 := by
    rw [integral_neg_eq_self P volume]
    exact hPi
  have hC : Integrable (fun t : ℝ => 25 * (1 / 4 + t ^ 2)⁻¹) :=
    cauchy_kernel_integral.1.const_mul 25
  have hmajor (t : ℝ) : f t ^ 2 / (1 / 4 + t ^ 2) ≤
      25 * (1 / 4 + t ^ 2)⁻¹ + (P t + P (-t)) := by
    have hd : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
    by_cases ht : |t| ≤ 4
    · have hs : f t ^ 2 ≤ 25 := by nlinarith [h0 t, hsmall t ht]
      calc
        _ ≤ 25 / (1 / 4 + t ^ 2) := div_le_div_of_nonneg_right hs hd.le
        _ ≤ _ := by rw [div_eq_mul_inv]; linarith [hPn t, hPn (-t)]
    · have ht' : 4 < |t| := not_le.mp ht
      have hu : 0 ≤ log |t| + 4 := (h0 t).trans (hlarge t ht')
      have hs : f t ^ 2 ≤ (log |t| + 4) ^ 2 :=
        (sq_le_sq₀ (h0 t) hu).mpr (hlarge t ht')
      have ht0 : t ^ 2 > 0 := by
        have := sq_abs t
        nlinarith [sq_nonneg (|t| - 4)]
      have hdiv : f t ^ 2 / (1 / 4 + t ^ 2) ≤ (log |t| + 4) ^ 2 / t ^ 2 :=
        (div_le_div_of_nonneg_right hs hd.le).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) ht0 (by linarith))
      have htail : P t + P (-t) = (log |t| + 4) ^ 2 / t ^ 2 := by
        rcases lt_or_ge t 0 with hn | hp
        · have ht4 : 4 < -t := by simpa only [abs_of_neg hn] using ht'
          simp [P, ht4, show ¬ 4 < t by linarith, abs_of_neg hn]
        · have ht4 : 4 < t := by simpa only [abs_of_nonneg hp] using ht'
          simp [P, ht4, show ¬ 4 < -t by linarith, abs_of_nonneg hp]
      rw [htail]
      linarith [show 0 ≤ 25 * (1 / 4 + t ^ 2)⁻¹ by positivity]
  have hM := hC.add (hP.add hN)
  have hk : Continuous (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    positivity
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f t ^ 2 / (1 / 4 + t ^ 2)) := by
    convert (hf.pow 2).mul hk.aestronglyMeasurable using 1
    ext t
    simp only [Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv]
  have hi : Integrable (fun t : ℝ => f t ^ 2 / (1 / 4 + t ^ 2)) := by
    apply hM.mono' hmeas
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity)]
    exact hmajor t
  refine ⟨hi, ?_⟩
  have hbound := integral_mono_ae hi hM (Filter.Eventually.of_forall hmajor)
  simp only [Pi.add_apply] at hbound
  have hadd := integral_add hC (hP.add hN)
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hP hN, integral_const_mul, cauchy_kernel_integral.2] at hbound
  linarith

/-- The logarithmic envelope on the left line suffices for coefficient 6.01.
CONDITIONAL ON hpoint, the explicit pointwise analytic estimate.
This is a sufficient scalar comparison for P0014 page 35.
Its input envelope constant three is stronger than display 4.12 at q equal to one.
-/
theorem contour_energy_of_log_envelope (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (h0 : ∀ t : ℝ, 0 ≤ f t)
    (hpoint : ∀ t : ℝ, f t ≤ (1 / 2) * log (t ^ 2 + 9 / 4) + 3) :
    Integrable (fun t : ℝ => f t ^ 2 / (1 / 4 + t ^ 2)) ∧
      (∫ t : ℝ, f t ^ 2 / (1 / 4 + t ^ 2)) ≤ 6.01 ^ 2 * (2 * π) := by
  have hsmall (t : ℝ) (ht : |t| ≤ 4) : f t ≤ 5 := by
    have hs := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 4)).mpr ht
    rw [sq_abs] at hs
    have hl : log (t ^ 2 + 9 / 4) ≤ log ((2 : ℝ) ^ 5) :=
      log_le_log (by positivity) (by norm_num; linarith)
    rw [log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith [hpoint t, log_two_lt_d9]
  have hlarge (t : ℝ) (ht : 4 < |t|) : f t ≤ log |t| + 4 := by
    have hp : 0 < |t| := by linarith
    have hs := sq_abs t
    have hsq : 16 < t ^ 2 := by nlinarith [sq_nonneg (|t| - 4)]
    have hl : log (t ^ 2 + 9 / 4) ≤ log (4 * |t| ^ 2) :=
      log_le_log (by positivity) (by nlinarith)
    rw [log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hp.ne'), log_pow] at hl
    have hl4 : log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [log_two_lt_d9]
    norm_num only [Nat.cast_ofNat] at hl
    linarith [hpoint t]
  obtain ⟨hi, hb⟩ := scalar_contour_energy f hf h0 hsmall hlarge
  refine ⟨hi, hb.trans ?_⟩
  nlinarith [pi_gt_three]

end LeanLab.HelfgottMajor.Contour472

#print axioms LeanLab.HelfgottMajor.Contour472.log_square_tail_derivative
#print axioms LeanLab.HelfgottMajor.Contour472.log_square_tail_primitive_tendsto
#print axioms LeanLab.HelfgottMajor.Contour472.log_square_tail_integral
#print axioms LeanLab.HelfgottMajor.Contour472.log_square_tail_four_le
#print axioms LeanLab.HelfgottMajor.Contour472.cauchy_kernel_integral
#print axioms LeanLab.HelfgottMajor.Contour472.scalar_contour_energy
#print axioms LeanLab.HelfgottMajor.Contour472.contour_energy_of_log_envelope
