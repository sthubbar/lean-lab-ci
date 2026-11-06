import LeanLab.ChirreHagen2025.Decomp377d
import LeanLab.ChirreHagen2025.GammaGeometry429
import LeanLab.ChirreHagen2025.LogKernel429

/-!
P0075 page 4 and Chandee Appendix pages 12 and 13, display 24.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429a
open MeasureTheory Decomp377d

/-- Chandee page 12, the preliminary sign region before Case 1. -/
theorem kernel_nonpos (z : ℂ) (u : ℝ) (hu : 0 < u)
    (hxy : z.im ^ 2 ≤ z.re ^ 2) : binetKernel z u ≤ 0 := by
  unfold binetKernel
  apply div_nonpos_of_nonpos_of_nonneg
  · have : 0 ≤ u ^ 2 + z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg u]
    nlinarith
  · have he : 0 ≤ Real.exp (2 * Real.pi * u) - 1 := by
      have := Real.one_le_exp (show 0 ≤ 2 * Real.pi * u by positivity)
      linarith
    positivity

/-- Chandee page 12, the preliminary sign argument for the full correction. -/
theorem correction_nonpos_of_im_sq_le (z : ℂ) (hz : 0 ≤ z.re)
    (hxy : z.im ^ 2 ≤ z.re ^ 2) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  have hi : binetRemainder z ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ioi
    intro u hu
    exact kernel_nonpos z u hu hxy
  have hr : 0 ≤ (1 / (2 * z)).re := by
    norm_num [Complex.div_re, Complex.normSq_mul]
    exact mul_nonneg hz (inv_nonneg.mpr (Complex.normSq_nonneg z))
  linarith

/-- Chandee page 13, the scalar last inequality after display 24. -/
theorem exponential_absorption (r : ℝ) (hr : 4 ≤ r) :
    15 / (128 * r ^ 2) +
      4 * Real.exp (-2 * Real.pi * r / 3) / 3 * (1 + 1 / r ^ 2) ≤
      1 / (8 * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hbase : (512 / 3 * 17 : ℝ) ≤ Real.exp 8 := by
    calc
      (512 / 3 * 17 : ℝ) ≤ (2.718 : ℝ) ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := by
        gcongr
        linarith [Real.exp_one_gt_d9]
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hlin : r - 3 ≤ Real.exp (r - 4) := by
    linarith [Real.add_one_le_exp (r - 4)]
  have hsq := pow_le_pow_left₀ (show 0 ≤ r - 3 by linarith) hlin 2
  have hpoly : r ^ 2 + 1 ≤ 17 * (r - 3) ^ 2 := by
    nlinarith [sq_nonneg (r - 4)]
  have hexp : (512 / 3 : ℝ) * (r ^ 2 + 1) ≤ Real.exp (2 * Real.pi * r / 3) := by
    calc
      _ ≤ (512 / 3 * 17) * (r - 3) ^ 2 := by nlinarith
      _ ≤ Real.exp 8 * Real.exp (r - 4) ^ 2 :=
        mul_le_mul hbase hsq (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * r) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have he0 : 0 < Real.exp (2 * Real.pi * r / 3) := Real.exp_pos _
  rw [show -2 * Real.pi * r / 3 = -(2 * Real.pi * r / 3) by ring,
    Real.exp_neg]
  apply (le_div_iff₀ (show 0 < 8 * r ^ 2 by positivity)).mpr
  field_simp
  rw [show r * 2 * Real.pi / 3 = 2 * Real.pi * r / 3 by ring]
  nlinarith

/-- Chandee page 13, the nonnegative integrand after integration by parts. -/
noncomputable def partsKernel (z : ℂ) (u : ℝ) : ℝ :=
  ‖z ^ 2 - (u : ℂ) ^ 2‖ / ‖(u : ℂ) ^ 2 + z ^ 2‖ ^ 2 *
    Real.log (1 / (1 - Real.exp (-2 * Real.pi * u)))

/-- LEAF. Chandee Appendix page 13, first display after display 24.
Integration by parts and the norm inequality split the Binet remainder
at norm z over three. Integrability of both resulting pieces is explicit.
No numerical bound for either piece occurs here. -/
theorem binet_split (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    IntegrableOn (partsKernel z) (Set.Ioc 0 (‖z‖ / 3)) ∧
    IntegrableOn (partsKernel z) (Set.Ioi (‖z‖ / 3)) ∧
    binetRemainder z ≤
      (1 / Real.pi) * (∫ u in Set.Ioc 0 (‖z‖ / 3), partsKernel z u) +
      (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) := by
  sorry

/-- LEAF. Chandee Appendix page 13, first integral estimate after display 24.
The local norm ratio is at most 45 divided by 32 norm z squared. The
logarithmic kernel integral supplies the factor pi over twelve. -/
theorem parts_head (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    (1 / Real.pi) * (∫ u in Set.Ioc 0 (‖z‖ / 3), partsKernel z u) ≤
      15 / (128 * ‖z‖ ^ 2) := by
  let C : ℝ := 45 / (32 * ‖z‖ ^ 2)
  have hz0 : z ≠ 0 := by
    intro he
    norm_num [he] at hn
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsub : Set.Ioc (0 : ℝ) (‖z‖ / 3) ⊆ Set.Ioi 0 := by
    intro u hu
    exact hu.1
  have hg := LogKernel429.log_kernel_integrable.mono_set hsub
  have hi := hg.const_mul C
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) (‖z‖ / 3)) :
      partsKernel z u ≤ C * LogKernel429.logKernel u := by
    have hh := mul_le_mul_of_nonneg_right
      (GammaGeometry429.head_norm_ratio z hz0 u hu.1.le hu.2)
      (LogKernel429.log_kernel_nonneg u hu.1)
    simpa only [partsKernel, LogKernel429.logKernel, C] using hh
  have hnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ partsKernel z u := by
    have hh := LogKernel429.log_kernel_nonneg u hu
    change 0 ≤ _ * LogKernel429.logKernel u
    positivity
  have hm : Measurable (partsKernel z) := by
    unfold partsKernel
    fun_prop
  have hp : IntegrableOn (partsKernel z) (Set.Ioc (0 : ℝ) (‖z‖ / 3)) := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u hu.1)]
    exact hpoint u hu
  have hhead : (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), partsKernel z u) ≤
      C * (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), LogKernel429.logKernel u) := by
    calc
      _ ≤ ∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), C * LogKernel429.logKernel u :=
        setIntegral_mono_on hp hi measurableSet_Ioc hpoint
      _ = _ := integral_const_mul C _
  have hlog : (∫ u in Set.Ioc (0 : ℝ) (‖z‖ / 3), LogKernel429.logKernel u) ≤ Real.pi / 12 := by
    rw [← LogKernel429.log_kernel_integral]
    apply setIntegral_mono_set LogKernel429.log_kernel_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact LogKernel429.log_kernel_nonneg u hu
    · exact Filter.Eventually.of_forall hsub
  calc
    _ ≤ (1 / Real.pi) * (C * (Real.pi / 12)) :=
      mul_le_mul_of_nonneg_left
        (hhead.trans (mul_le_mul_of_nonneg_left hlog hC)) (by positivity)
    _ = _ := by
      dsimp [C]
      have hn0 : ‖z‖ ≠ 0 := by linarith
      field_simp [Real.pi_ne_zero, hn0]
      ring

/-- LEAF. Chandee Appendix page 13, second integral estimate after display 24.
The denominator factorization and the exponential logarithm tail bound
control only the unbounded piece. -/
theorem parts_tail (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    (1 / Real.pi) * (∫ u in Set.Ioi (‖z‖ / 3), partsKernel z u) ≤
      4 * Real.exp (-2 * Real.pi * ‖z‖ / 3) / 3 * (1 + 1 / ‖z‖ ^ 2) := by
  sorry

/-- Chandee display 24, assembled from the three smaller integral leaves.
CONDITIONAL ON those leaves. -/
theorem binet_large_majorant (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hn : 4 ≤ ‖z‖) (hxy : z.re ^ 2 < z.im ^ 2) :
    binetRemainder z ≤ 15 / (128 * ‖z‖ ^ 2) +
      4 * Real.exp (-2 * Real.pi * ‖z‖ / 3) / 3 * (1 + 1 / ‖z‖ ^ 2) := by
  exact (binet_split z hz hn hxy).2.2 |>.trans
    (add_le_add (parts_head z hz hn hxy) (parts_tail z hz hn hxy))

/-- Chandee page 13, the reciprocal contribution before the final inequality. -/
theorem reciprocal_lower (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    1 / (8 * ‖z‖ ^ 2) ≤ (1 / (2 * z)).re := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (hz.trans (Complex.re_le_norm z))
  have hn : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  norm_num [Complex.div_re, Complex.normSq_mul, hn]
  have hn0 : ‖z‖ ^ 2 ≠ 0 := (sq_pos_of_pos hz0).ne'
  field_simp
  nlinarith [sq_pos_of_pos hz0]

/-- Exact existing Decomp377d.large_correction statement.
CONDITIONAL ON the smaller display 24 remainder estimate. -/
theorem large_correction (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) (hn : 4 ≤ ‖z‖) :
    -(1 / (2 * z)).re + binetRemainder z ≤ 0 := by
  by_cases hxy : z.im ^ 2 ≤ z.re ^ 2
  · exact correction_nonpos_of_im_sq_le z (by linarith) hxy
  · have h := (binet_large_majorant z hz hn (lt_of_not_ge hxy)).trans
      (exponential_absorption ‖z‖ hn)
    linarith [reciprocal_lower z hz]

end LeanLab.ChirreHagen2025.Decomp429a
