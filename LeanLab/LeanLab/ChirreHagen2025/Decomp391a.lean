import LeanLab.ChirreHagen2025.Decomp429e
import LeanLab.PNTPort.ExplicitPsi1.ZeroSum

/-!
Supply for Decomp358d.mangoldt_large_range through the existing Decomp429e split.
JRT 2023 page 3 Lemma 9 and page 4 Lemma 10.
Chirre, Hagen and Simonic page 4 equation 3.3 and Remark 7.
Ramare 2013 pages 118 to 120, equation 5.1 and its zero estimate.
https://arxiv.org/abs/2303.13785
https://arxiv.org/abs/2206.00819
https://doi.org/10.4064/aa159-2-2
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp391a
open ArithmeticFunction MeasureTheory Set Filter

/-- CHS page 4 equation 3.3, a zero term with analytic multiplicity.
The subtype includes every nontrivial zero in the open critical strip. -/
noncomputable def zeroTerm (x : ℝ)
    (ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ : ℂ) *
    (x : ℂ) ^ ((ρ : ℂ) - 1) / ((ρ : ℂ) * ((ρ : ℂ) - 1))

/-- CHS page 4 equation 3.3, the elementary remainder integrand. -/
noncomputable def remainderKernel (u : ℝ) : ℝ :=
  (Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - 1 / u ^ 2)) / u ^ 2

/-- JRT page 3 Lemma 9, inverse-square integration on a positive tail. -/
theorem inverse_square_tail (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ioi x) ∧
      (∫ u in Ioi x, 1 / u ^ 2) = 1 / x := by
  have heq : (fun u : ℝ => u ^ (-2 : ℝ)) =ᵐ[volume.restrict (Ioi x)]
      (fun u : ℝ => 1 / u ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.rpow_neg (hx.trans hu).le, Real.rpow_two]
    simp only [one_div]
  constructor
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).congr heq
  · rw [← integral_congr_ae heq, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx]
    norm_num [Real.rpow_neg_one]

/-- JRT page 3 Lemma 9, the logarithmic correction is nonpositive. -/
theorem remainderKernel_le (u : ℝ) (hu : 1 < u) :
    remainderKernel u ≤ Real.log (2 * Real.pi) / u ^ 2 := by
  have hu2 : 1 < u ^ 2 := by nlinarith
  have hq : 0 < 1 / u ^ 2 := by positivity
  have hq1 : 1 / u ^ 2 < 1 := (div_lt_one (by positivity)).mpr hu2
  have hl := Real.log_nonpos (by linarith : 0 ≤ 1 - 1 / u ^ 2)
    (by linarith : 1 - 1 / u ^ 2 ≤ 1)
  unfold remainderKernel
  apply div_le_div_of_nonneg_right _ (sq_nonneg u)
  linarith

/-- JRT page 3 Lemma 9, actual integrability of its elementary remainder. -/
theorem remainder_integrable (x : ℝ) (hx : 1 < x) :
    IntegrableOn remainderKernel (Ioi x) := by
  have hx0 : 0 < x := by linarith
  have hbase : 0 < 1 - 1 / x ^ 2 := by
    have h : 1 / x ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  have harg (u : ℝ) (hu : u ∈ Ioi x) :
      1 - 1 / x ^ 2 ≤ 1 - 1 / u ^ 2 ∧ 1 - 1 / u ^ 2 ≤ 1 := by
    have hxu : x ^ 2 ≤ u ^ 2 := by
      have hxu : x < u := hu
      nlinarith
    have hh := one_div_le_one_div_of_le (by positivity : 0 < x ^ 2) hxu
    constructor <;> linarith [show 0 ≤ 1 / u ^ 2 by positivity]
  have hden : ContinuousOn (fun u : ℝ => u ^ 2) (Ioi x) := continuousOn_id.pow 2
  have hnz (u : ℝ) (hu : u ∈ Ioi x) : u ^ 2 ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (hx0.trans hu))
  have hinv : ContinuousOn (fun u : ℝ => 1 / u ^ 2) (Ioi x) :=
    continuousOn_const.div hden hnz
  have hlog : ContinuousOn (fun u : ℝ => Real.log (1 - 1 / u ^ 2)) (Ioi x) :=
    (continuousOn_const.sub hinv).log (fun u hu => ne_of_gt (hbase.trans_le (harg u hu).1))
  have hcont : ContinuousOn remainderKernel (Ioi x) :=
    (continuousOn_const.add (continuousOn_const.mul hlog)).div hden hnz
  let C := |Real.log (2 * Real.pi)| + |Real.log (1 - 1 / x ^ 2)|
  apply ((inverse_square_tail x hx0).1.const_mul C).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hx0.trans hu
  have ha := harg u hu
  have hlo := Real.log_le_log hbase ha.1
  have hhi := Real.log_nonpos (hbase.le.trans ha.1) ha.2
  have hlabs : |Real.log (1 - 1 / u ^ 2)| ≤ |Real.log (1 - 1 / x ^ 2)| := by
    rw [abs_of_nonpos hhi, abs_of_nonpos (hlo.trans hhi)]
    linarith
  rw [Real.norm_eq_abs, remainderKernel, abs_div, abs_of_nonneg (sq_nonneg u)]
  have hn : |Real.log (2 * Real.pi) + 1 / 2 * Real.log (1 - 1 / u ^ 2)| ≤ C := by
    calc
      _ ≤ |Real.log (2 * Real.pi)| + |1 / 2 * Real.log (1 - 1 / u ^ 2)| := abs_add_le _ _
      _ ≤ C := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        dsimp [C]
        linarith [abs_nonneg (Real.log (1 - 1 / x ^ 2))]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hn (sq_nonneg u)

/-- JRT page 3 Lemma 9, a one-sided remainder bound needs no 0.0001 loss. -/
theorem remainder_integral_le (x : ℝ) (hx : 1 < x) :
    (∫ u in Ioi x, remainderKernel u) ≤ Real.log (2 * Real.pi) / x := by
  have hi := inverse_square_tail x (by linarith)
  have hh : (∫ u in Ioi x, remainderKernel u) ≤
      ∫ u in Ioi x, Real.log (2 * Real.pi) * (1 / u ^ 2) :=
    integral_mono_ae (remainder_integrable x hx)
    (hi.1.const_mul (Real.log (2 * Real.pi)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa only [mul_one_div] using remainderKernel_le u (hx.trans hu))
  rw [integral_const_mul, hi.2] at hh
  simpa only [mul_one_div] using hh

/-- JRT page 3 proof of Lemma 9, the elementary 0.0001 allowance at 71. -/
theorem half_log_correction (u : ℝ) (hu : 71 ≤ u) :
    1 / 2 * |Real.log (1 - 1 / u ^ 2)| ≤ 0.0001 := by
  have hu2 : (5041 : ℝ) ≤ u ^ 2 := by nlinarith
  have hq : 1 / u ^ 2 ≤ (1 / 5041 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hu2
  have hq0 : 0 ≤ 1 / u ^ 2 := by positivity
  have hb : (5040 / 5041 : ℝ) ≤ 1 - 1 / u ^ 2 := by linarith
  have hp : 0 < 1 - 1 / u ^ 2 := lt_of_lt_of_le (by norm_num) hb
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5040 / 5041) hb
  norm_num only [one_div_div, one_div] at hi
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hh := Real.log_nonpos hp.le (by linarith : 1 - 1 / u ^ 2 ≤ 1)
  rw [abs_of_nonpos hh]
  simp only [one_div] at hl ⊢
  linarith

/-- JRT page 3 proof of Lemma 9, the full elementary remainder envelope. -/
theorem remainder_abs_pointwise (u : ℝ) (hu : 71 ≤ u) :
    |remainderKernel u| ≤ (Real.log (2 * Real.pi) + 0.0001) / u ^ 2 := by
  have hl : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc := half_log_correction u hu
  rw [remainderKernel, abs_div, abs_of_nonneg (sq_nonneg u)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg u)
  calc
    _ ≤ |Real.log (2 * Real.pi)| + |1 / 2 * Real.log (1 - 1 / u ^ 2)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hl, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

/-- JRT page 3 proof of Lemma 9, the absolute integral bound with convergence. -/
theorem remainder_integral_abs_le (x : ℝ) (hx : 71 ≤ x) :
    |∫ u in Ioi x, remainderKernel u| ≤ (Real.log (2 * Real.pi) + 0.0001) / x := by
  have hi := inverse_square_tail x (by linarith)
  have hrem : IntegrableOn (fun u => |remainderKernel u|) (Ioi x) := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using (remainder_integrable x (by linarith)).norm
  have hh : (∫ u in Ioi x, |remainderKernel u|) ≤
      ∫ u in Ioi x, (Real.log (2 * Real.pi) + 0.0001) * (1 / u ^ 2) := by
    apply integral_mono_ae hrem (hi.1.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [mul_one_div] using remainder_abs_pointwise u (hx.trans hu.le)
  rw [integral_const_mul, hi.2] at hh
  exact abs_integral_le_integral_abs.trans (by simpa only [mul_one_div] using hh)

/-- Comparison of shifted zero denominators outside a disk. -/
theorem shifted_denominator_comparison (z : ℂ) (hz : 2 ≤ ‖z‖) :
    ‖z + 1‖ ≤ 3 * ‖z - 1‖ := by
  have hm := norm_sub_norm_le z (1 : ℂ)
  simp only [norm_one] at hm
  have hh := norm_add_le (z - 1) (2 : ℂ)
  rw [show z - 1 + 2 = z + 1 by ring] at hh
  norm_num at hh
  linarith

/-- CHS page 4 equation 3.3, comparison with the convergent zero-count weight. -/
theorem zero_term_norm_le (x : ℝ) (hx : 1 ≤ x)
    (ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1})
    (hρ : 2 ≤ ‖(ρ : ℂ)‖) :
    ‖zeroTerm x ρ‖ ≤
      3 * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
  have hx0 : 0 < x := by linarith
  have hz0 : (ρ : ℂ) ≠ 0 := by intro h; have := ρ.2.2.1; simp [h] at this
  have hzm : (ρ : ℂ) - 1 ≠ 0 := by
    intro h
    have hh : (ρ : ℂ) = 1 := sub_eq_zero.mp h
    have := ρ.2.2.2
    simp [hh] at this
  have hzp : (ρ : ℂ) + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    have := ρ.2.2.1
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  have hdm : 0 < ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖ := norm_pos_iff.mpr (mul_ne_zero hz0 hzm)
  have hdp : 0 < ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := norm_pos_iff.mpr (mul_ne_zero hz0 hzp)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hx (sub_nonpos.mpr ρ.2.2.2.le)
  have hc := shifted_denominator_comparison ρ hρ
  rw [zeroTerm, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖ := by
      apply div_le_div_of_nonneg_right _ hdm.le
      simpa using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ))
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hdm hdp).mpr
      calc
        _ = ((analyticOrderNatAt riemannZeta ρ : ℝ) * ‖(ρ : ℂ)‖) * ‖(ρ : ℂ) + 1‖ := by
          rw [norm_mul]; ring
        _ ≤ ((analyticOrderNatAt riemannZeta ρ : ℝ) * ‖(ρ : ℂ)‖) * (3 * ‖(ρ : ℂ) - 1‖) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := by rw [norm_mul]; ring

/-- CHS page 4 equation 3.3, absolute convergence of its zero expansion. -/
theorem zero_series_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (zeroTerm x) := by
  let i : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} →
      LeanLab.PNTPort.ExplicitPsi1.Zall :=
    fun ρ => ⟨ρ, ρ.2.1, by linarith [ρ.2.2.1]⟩
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : LeanLab.PNTPort.ExplicitPsi1.Zall => (z : ℂ)) h
  have hw : Summable (fun ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by
    simpa [i, Function.comp_def, LeanLab.PNTPort.ExplicitPsi1.hw] using
      (LeanLab.PNTPort.ExplicitPsi1.summable_hw.comp_injective hi)
  have hc := (isCompact_closedBall (0 : ℂ) 2).inter_riemannZetaZeros_finite
  have hpre : ((fun ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} => (ρ : ℂ)) ⁻¹'
      (Metric.closedBall (0 : ℂ) 2 ∩ riemannZetaZeros)).Finite :=
    hc.preimage (fun a _ b _ h => Subtype.ext h)
  have hf : {ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} | ¬ 2 ≤ ‖(ρ : ℂ)‖}.Finite := by
    apply hpre.subset
    intro ρ hρ
    refine ⟨?_, ρ.2.1⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_not_ge hρ).le
  apply (hw.mul_left 3).of_norm_bounded_eventually
  filter_upwards [eventually_cofinite.mpr hf] with ρ hρ
  simpa only [zeroTerm] using zero_term_norm_le x hx ρ hρ

/-- LEAF. CHS page 4 equation 3.3 and Remark 7.
This is the exact corrected explicit formula without a quantitative psi bound.
Absolute convergence is part of the statement to rule out a default tsum. -/
theorem weighted_explicit_formula (x : ℝ) (hx : 100000 ≤ x) :
    Summable (zeroTerm x) ∧
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Real.log x - Real.eulerMascheroniConstant + (Chebyshev.psi x - x) / x -
        (∑' ρ, zeroTerm x ρ).re + ∫ u in Ioi x, remainderKernel u := by
  constructor
  · exact zero_series_summable x (by linarith)
  · exact?

/-- LEAF. Ramare pages 118 to 120, equation 5.1 and its following estimates.
This controls only the zero contribution. It contains no Mangoldt sum or psi.
The branch transition is on log x as written on page 119. -/
theorem zero_sum_bound (x : ℝ) (hx : 100000 ≤ x) :
    ‖∑' ρ, zeroTerm x ρ‖ ≤ 0.047 / Real.sqrt x + Decomp429e.zeroTailError x := by
  sorry

/-- Exact existing Decomp429e transfer statement.
CONDITIONAL ON the corrected explicit formula and the zero estimate. -/
theorem mangoldt_psi_transfer (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x +
        Real.eulerMascheroniConstant ≤
      |Chebyshev.psi x - x| / x + 0.047 / Real.sqrt x +
        (Real.log (2 * Real.pi) + 0.0001) / x + Decomp429e.zeroTailError x := by
  have hx0 : 0 < x := by linarith
  have hpsi := div_le_div_of_nonneg_right (le_abs_self (Chebyshev.psi x - x)) hx0.le
  have hz := Complex.re_le_norm (-(∑' ρ, zeroTerm x ρ))
  simp only [Complex.neg_re, norm_neg] at hz
  have hb := zero_sum_bound x hx
  have hi := remainder_integral_le x (by linarith)
  rw [(weighted_explicit_formula x hx).2]
  have hc : Real.log (2 * Real.pi) / x ≤ (Real.log (2 * Real.pi) + 0.0001) / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith
  linarith

/-- Exact sealed Decomp358d large-range statement.
CONDITIONAL ON two explicit-formula inputs and the two existing pure psi leaves.
The scalar budget is the existing proved Decomp429e theorem. -/
theorem mangoldt_large_range (m : ℕ) (hm : 100000 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        0.67 / Real.log (m : ℝ) ^ 2 := by
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hpsi : |Chebyshev.psi m - (m : ℝ)| / (m : ℝ) ≤
      if (m : ℝ) ≤ 10 ^ 19 then 0.94 / Real.sqrt m else 0.64673 / Real.log (m : ℝ) ^ 2 := by
    split_ifs with hsmall
    · have hp := Decomp429e.psi_finite_range m hm' hsmall
      have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
      calc
        _ ≤ (0.94 * Real.sqrt m) / (m : ℝ) := div_le_div_of_nonneg_right hp hm0.le
        _ = _ := by field_simp; nlinarith [Real.sq_sqrt hm0.le]
    · have hp := Decomp429e.psi_logarithmic_error m hm'
      have hh := div_le_div_of_nonneg_right hp hm0.le
      convert hh using 1 <;> field_simp
  have ht := mangoldt_psi_transfer m hm'
  simp only [Nat.floor_natCast] at ht
  have hb := Decomp429e.transfer_numeric_budget m hm'
  linarith

end LeanLab.ChirreHagen2025.Decomp391a
