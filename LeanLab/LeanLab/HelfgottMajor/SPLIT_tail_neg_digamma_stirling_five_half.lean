import Mathlib
import LeanLab.HelfgottMajor.Prep1122BinetSplit

/-!
Route burst S4, burst-20261124, unit S4-06. Split of the LEAF
`Decomp457b.tail_neg_digamma_stirling_five_half` of
`HelfgottMajor/SPLIT_principal_log_weight_tail_neg_digamma_envelope.lean`, the gamma factor
step of P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, page 34 display
4.10, where Binet's formula for the digamma function, DLMF 5.9.13, is quoted.

Route, exactly the one written in the doc comment of the target leaf:
* proved, Binet's second form with two correction terms: for `0 < re w`,
  `ψ(w) = log w - 1/(2w) - 1/(12 w^2) - ∫_0^∞ (f(x) - x/12) e^{-wx} dx` with
  `f(x) = 1/(e^x - 1) - 1/x + 1/2`; this is DLMF 5.9.13, already PROVED in the lab as
  `Prep1122BinetSplit.digamma_log_laplace`, together with
  `∫_0^∞ x e^{-wx} dx = 1/w^2`, `laplace_id_complex`, proved here by integration by parts;
* LEAF, the kernel bound `|f(x) - x/12| ≤ x^3/720` for `x > 0`;
* proved here: the Laplace estimate `∫_0^∞ x^3/720 e^{-(5/2)x} dx = 6/(720 (5/2)^4) = 2/9375`,
  through Mathlib's Gamma integral, and the assembly closing the exact target statement.
No new definition. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Complex MeasureTheory Set

/-- The Laplace transform of `x` on the right half plane, the step
`∫_0^∞ x e^{-wx} dx = 1/w^2` that takes the second correction term `-1/(12 w^2)` out of the
Binet integral DLMF 5.9.13, quoted on P0014 page 34 at display 4.10. Proved by integration by
parts on `Ioi 0` against `∫_0^∞ e^{-wx} dx = 1/w`. -/
theorem laplace_id_complex (w : ℂ) (hw : 0 < w.re) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) * cexp (-(w * x)) = 1 / w ^ 2 := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hE : IntegrableOn (fun x : ℝ => cexp (-w * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
  have hEv : ∫ x in Ioi (0 : ℝ), cexp (-w * x) = 1 / w := by
    rw [integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -cexp (-(w * y)) / w)
      (cexp (-(w * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(w * (y : ℂ))) (-(w * 1)) x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul w).neg
    have h2 := (h1.cexp.neg).div_const w
    convert h2 using 1
    field_simp
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
    fun x _ => Complex.ofRealCLM.hasDerivAt
  have hX : IntegrableOn (fun x : ℝ => (x : ℂ) * cexp (-(w * x))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := w.re)
      (by norm_num) (by norm_num) hw
    simp only [Real.rpow_one] at h
    have hm : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) * cexp (-(w * x)))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine Measurable.aestronglyMeasurable ?_
      fun_prop
    refine Integrable.mono' h hm ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hre : (-(w * (x : ℂ))).re = -w.re * x := by simp
    rw [hre]
  have hUV : IntegrableOn (fun x : ℝ => 1 * (-cexp (-(w * x)) / w)) (Ioi 0) := by
    have : (fun x : ℝ => 1 * (-cexp (-(w * x)) / w)) =
        fun x : ℝ => (-1 / w) * cexp (-w * x) := by
      funext x; ring_nf
    rw [this]
    exact hE.const_mul _
  have h0 : Filter.Tendsto ((fun y : ℝ => (y : ℂ)) * fun y : ℝ => -cexp (-(w * y)) / w)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : Continuous ((fun y : ℝ => (y : ℂ)) * fun y : ℝ => -cexp (-(w * y)) / w) := by
      show Continuous (fun y : ℝ => (y : ℂ) * (-cexp (-(w * y)) / w))
      fun_prop
    have := hc.continuousAt (x := 0) |>.tendsto
    simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinf : Filter.Tendsto ((fun y : ℝ => (y : ℂ)) * fun y : ℝ => -cexp (-(w * y)) / w)
      Filter.atTop (nhds 0) := by
    have hr := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 w.re hw
    have hr2 := hr.div_const ‖w‖
    rw [zero_div] at hr2
    refine squeeze_zero_norm' ?_ hr2
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_div, norm_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx, Real.rpow_one]
    have hre : (-(w * (x : ℂ))).re = -w.re * x := by simp
    rw [hre, mul_div_assoc]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hX hUV h0 hinf
  rw [hibp]
  have hcong : ∫ x in Ioi (0 : ℝ), (1 : ℂ) * (-cexp (-(w * x)) / w) =
      (-1 / w) * ∫ x in Ioi (0 : ℝ), cexp (-w * x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring_nf
  rw [hcong, hEv]
  field_simp
  ring

/-- The kernel of DLMF 5.9.13 lies in `[-1, 0]` for positive `x`; a copy of the private
`Prep1122BinetSplit.kernel_bound_1122b`. -/
theorem binet_laplace_kernel_bound (t : ℝ) (ht : 0 < t) :
    -1 ≤ 1 / t - 1 / (1 - Real.exp (-t)) ∧ 1 / t - 1 / (1 - Real.exp (-t)) ≤ 0 := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h3 : (1 + t) * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    have hm : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-t)]
  have hd : 0 < 1 - Real.exp (-t) := by linarith
  constructor
  · rw [div_sub_div _ _ ht.ne' hd.ne', le_div_iff₀ (mul_pos ht hd)]
    nlinarith
  · rw [sub_nonpos, div_le_div_iff₀ ht hd]
    linarith

/-- Integrability of the DLMF 5.9.13 Laplace integrand, as in the private
`Prep1122BinetSplit.kernel_laplace_1122b`. -/
theorem binet_laplace_kernel_integrable (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ =>
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-w.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hb : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)‖ ≤
        Real.exp (-w.re * t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * w).re = -w.re * t := by simp; ring
    rw [hre]
    have hc : (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) =
        ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) := by push_cast; ring
    have hk : ‖1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))‖ ≤ 1 := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le]
      obtain ⟨a, b⟩ := binet_laplace_kernel_bound t ht
      exact ⟨a, by linarith⟩
    calc ‖1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))‖ * Real.exp (-w.re * t)
        ≤ 1 * Real.exp (-w.re * t) :=
          mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = Real.exp (-w.re * t) := one_mul _
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w))
        (volume.restrict (Ioi (0 : ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  exact Integrable.mono' hg hm hb

theorem laplace_id_complex_integrable (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * cexp (-(w * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := w.re)
    (by norm_num) (by norm_num) hw
  simp only [Real.rpow_one] at h
  have hm : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) * cexp (-(w * x)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  refine Integrable.mono' h hm ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hre : (-(w * (x : ℂ))).re = -w.re * x := by simp
  rw [hre]

/-- Binet's formula for the digamma function, DLMF 5.9.13, quoted on P0014 page 34 at
display 4.10, with the second correction term `-1/(12 w^2)` taken out of the integral:
for `0 < re w`, `ψ(w)` equals
`log w - 1/(2w) - 1/(12 w^2) - ∫_0^∞ (1/(e^x - 1) - 1/x + 1/2 - x/12) e^{-wx} dx`.
Proved from the proved Laplace form `Prep1122BinetSplit.digamma_log_laplace` and
`laplace_id_complex`. -/
theorem binet_digamma_second_correction (w : ℂ) (hw : 0 < w.re) :
    Complex.digamma w =
      Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2) -
        ∫ x in Ioi (0 : ℝ),
          ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12 : ℝ) : ℂ) * cexp (-(w * x)) := by
  have hD := Prep1122BinetSplit.digamma_log_laplace w hw
  have hK := binet_laplace_kernel_integrable w hw
  have hE : IntegrableOn (fun x : ℝ => cexp (-w * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
  have hEv : ∫ x in Ioi (0 : ℝ), cexp (-w * x) = 1 / w := by
    rw [integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg]
  have hX := laplace_id_complex_integrable w hw
  have hXv := laplace_id_complex w hw
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12 : ℝ) : ℂ) * cexp (-(w * x)) =
        -((1 / (x : ℂ) - 1 / (1 - (Real.exp (-x) : ℂ))) * Complex.exp (-(x : ℂ) * w)) -
          (1 / 2 : ℂ) * cexp (-w * x) - (1 / 12 : ℂ) * ((x : ℂ) * cexp (-(w * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have he1 : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx0
    have hr : (1 / x - 1 / (1 - Real.exp (-x))) =
        -(1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12) - 1 / 2 - x / 12 := by
      rw [Real.exp_neg]
      have hne : Real.exp x - 1 ≠ 0 := by linarith
      have hne2 : 1 - (Real.exp x)⁻¹ ≠ 0 := by
        have : (Real.exp x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ he1
        linarith
      have hpos : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
      field_simp
      ring
    have hc : (1 / (x : ℂ) - 1 / (1 - (Real.exp (-x) : ℂ))) =
        ((1 / x - 1 / (1 - Real.exp (-x)) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, hr]
    have e1 : Complex.exp (-(x : ℂ) * w) = cexp (-(w * x)) := by ring_nf
    have e2 : cexp (-w * x) = cexp (-(w * x)) := by ring_nf
    rw [e1, e2]
    push_cast
    ring
  have hI : ∫ x in Ioi (0 : ℝ),
      ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12 : ℝ) : ℂ) * cexp (-(w * x)) =
      -(∫ x in Ioi (0 : ℝ), (1 / (x : ℂ) - 1 / (1 - (Real.exp (-x) : ℂ))) *
          Complex.exp (-(x : ℂ) * w)) -
        (1 / 2 : ℂ) * (∫ x in Ioi (0 : ℝ), cexp (-w * x)) -
        (1 / 12 : ℂ) * ∫ x in Ioi (0 : ℝ), (x : ℂ) * cexp (-(w * x)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub, integral_sub, integral_neg,
      integral_const_mul, integral_const_mul]
    · exact hK.neg
    · exact hE.const_mul _
    · exact hK.neg.sub (hE.const_mul _)
    · exact hX.const_mul _
  rw [hI, hEv, hXv, hD]
  ring

/-- LEAF: the kernel bound behind the remainder `2/9375` of the target leaf, P0014 page 34
display 4.10 with DLMF 5.9.13: for `x > 0`,
`|1/(e^x - 1) - 1/x + 1/2 - x/12| ≤ x^3/720`, the first omitted Bernoulli term
`B_4 x^3/4!` of `x/(e^x - 1)`. Class MEDIUM: one real variable, the alternating Bernoulli
series or two derivative comparisons. -/
theorem binet_kernel_abs_le (x : ℝ) (hx : 0 < x) :
    |1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12| ≤ x ^ 3 / 720 := by
  sorry

/-- The Laplace integral of the kernel bound on the line of real part five halves:
`∫_0^∞ x^3/720 e^{-(5/2)x} dx = Γ(4)/(720 (5/2)^4) = 2/9375`. -/
theorem laplace_cube_five_half :
    ∫ x in Ioi (0 : ℝ), x ^ 3 / 720 * Real.exp (-(5 / 2 * x)) = 2 / 9375 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := 5 / 2) (by norm_num)
    (by norm_num)
  have hG : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hG] at h
  have hc : ∫ x in Ioi (0 : ℝ), x ^ 3 / 720 * Real.exp (-(5 / 2 * x)) =
      (1 / 720) * ∫ x in Ioi (0 : ℝ), x ^ ((4 : ℝ) - 1) * Real.exp (-(5 / 2 * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [show (4 : ℝ) - 1 = (3 : ℕ) by norm_num, Real.rpow_natCast]
    ring
  rw [hc, h, show (1 / (5 / 2 : ℝ)) ^ (4 : ℝ) = (2 / 5) ^ (4 : ℕ) by
    rw [← Real.rpow_natCast]; norm_num]
  norm_num

theorem laplace_cube_five_half_integrable :
    IntegrableOn (fun x : ℝ => x ^ 3 / 720 * Real.exp (-(5 / 2 * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 3) (p := 1) (b := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : IntegrableOn
      (fun x : ℝ => 1 / 720 * (x ^ (3 : ℝ) * Real.exp (-(5 / 2) * x ^ (1 : ℝ)))) (Ioi 0) :=
    h.const_mul (1 / 720)
  refine IntegrableOn.congr_fun h2 (fun x hx => ?_) measurableSet_Ioi
  rw [Real.rpow_one, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  ring_nf

/-- The target leaf `tail_neg_digamma_stirling_five_half`, closed from the Binet leaf and the
kernel leaf by the Laplace estimate above. -/
theorem tail_neg_digamma_stirling_five_half_of_leaves (t : ℝ) :
    ‖Complex.digamma ((5 / 2 : ℂ) + t * I) -
        (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))‖ ≤ 2 / 9375 := by
  set w : ℂ := (5 / 2 : ℂ) + t * I with hwdef
  have hwre : w.re = 5 / 2 := by simp [hwdef]
  have hB := binet_digamma_second_correction w (by rw [hwre]; norm_num)
  rw [hB]
  set g : ℝ → ℂ := fun x =>
    ((1 / (Real.exp x - 1) - 1 / x + 1 / 2 - x / 12 : ℝ) : ℂ) * cexp (-(w * x))
  rw [sub_sub_cancel_left, norm_neg, ← laplace_cube_five_half]
  refine norm_integral_le_of_norm_le laplace_cube_five_half_integrable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  have hk := binet_kernel_abs_le x hx0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-(w * (x : ℂ))).re = -(5 / 2 * x) := by
    simp [hwdef]
  rw [hre]
  exact mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le

end LeanLab.HelfgottMajor.Decomp457b
