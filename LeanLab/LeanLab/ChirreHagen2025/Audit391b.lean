import LeanLab.ChirreHagen2025.Statements

/-!
Scalar QUESTION about Ramare 2013 pages 119 and 120.
At log x divided by R equal to 2500, the auxiliary integral exceeds
its final printed majorant. This does not refute the Mangoldt statement.
https://doi.org/10.4064/aa159-2-2
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Audit391b
open MeasureTheory Set

/-- Ramare page 119, the u-integrand at log x divided by R equal to 2500. -/
noncomputable def saddleKernel (u : ℝ) : ℝ :=
  u * Real.exp (-2500 / u - u) / (2 * Real.pi)

/-- Ramare page 119, integrability of the auxiliary kernel on positive tails. -/
theorem saddle_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn saddleKernel (Ioi t) := by
  have hg : IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_rpow
      (s := 1) (p := 1) (by norm_num) (by norm_num))
  have hc : ContinuousOn saddleKernel (Ioi t) := by
    have hdiv : ContinuousOn (fun u : ℝ => -2500 / u - u) (Ioi t) :=
      (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt (ht.trans hu))).sub continuousOn_id
    exact (continuousOn_id.mul (Real.continuous_exp.comp_continuousOn hdiv)).div_const _
  apply ((hg.mono_set (Ioi_subset_Ioi ht.le)).div_const (2 * Real.pi)).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := ht.trans hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold saddleKernel; positivity)]
  unfold saddleKernel
  gcongr
  have hn : -2500 / u ≤ 0 := by apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  linarith

/-- Ramare page 120, a lower envelope on the interval from 48 to 52. -/
theorem saddle_interval_lower (u : ℝ) (hu : u ∈ Icc 48 52) :
    44 * Real.exp (-100) / (2 * Real.pi) ≤ saddleKernel u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hsq : (u - 50) ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2]
  have harg : -(100 : ℝ) - 1 / 12 ≤ -2500 / u - u := by
    have hh : 2500 / u ≤ 100 + 1 / 12 - u := by
      apply (div_le_iff₀ hu0).mpr
      nlinarith [hu.1]
    rw [neg_div]
    linarith
  have he : (11 / 12 : ℝ) * Real.exp (-100) ≤ Real.exp (-2500 / u - u) := by
    calc
      _ ≤ Real.exp (-100) * Real.exp (-(1 / 12 : ℝ)) := by
        have hh := Real.add_one_le_exp (-(1 / 12 : ℝ))
        nlinarith [Real.exp_pos (-100)]
      _ = Real.exp (-(100 : ℝ) - 1 / 12) := by rw [← Real.exp_add]; congr 1 <;> ring
      _ ≤ _ := Real.exp_le_exp.mpr harg
  unfold saddleKernel
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    44 * Real.exp (-100) ≤ u * ((11 / 12 : ℝ) * Real.exp (-100)) := by
      nlinarith [Real.exp_pos (-100), hu.1]
    _ ≤ _ := mul_le_mul_of_nonneg_left he hu0.le

/-- Ramare page 120, the auxiliary integral exceeds the printed final bound.
The hypothesis t at most 47 contains t equal to log of 2.44 times ten to twelve.
No hypothesis about zeta zeros occurs in this scalar counterexample. -/
theorem saddle_integral_exceeds_printed (t : ℝ) (ht : 0 < t) (httop : t ≤ 47) :
    101 / (2 * Real.pi) * Real.exp (-100) < ∫ u in Ioi t, saddleKernel u := by
  have hi := saddle_integrable t ht
  have hs : Icc (48 : ℝ) 52 ⊆ Ioi t := by intro u hu; have := hu.1; change t < u; linarith
  have hsmall : (∫ u in Icc (48 : ℝ) 52, (44 * Real.exp (-100) / (2 * Real.pi))) ≤
      ∫ u in Icc (48 : ℝ) 52, saddleKernel u := by
    apply integral_mono_ae (continuousOn_const.integrableOn_Icc) (hi.mono_set hs)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact saddle_interval_lower u hu
  have hlarge : (∫ u in Icc (48 : ℝ) 52, saddleKernel u) ≤ ∫ u in Ioi t, saddleKernel u := by
    apply setIntegral_mono_set hi _ (Filter.Eventually.of_forall hs)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    unfold saddleKernel
    have : 0 < u := ht.trans hu
    positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (48 : ℝ) ≤ 52),
    intervalIntegral.integral_const] at hsmall
  norm_num at hsmall
  have hp : 0 < Real.exp (-100) / (2 * Real.pi) := by positivity
  have hstrict : 101 / (2 * Real.pi) * Real.exp (-100) <
      4 * (44 * Real.exp (-100) / (2 * Real.pi)) := by
    calc
      _ = 101 * (Real.exp (-100) / (2 * Real.pi)) := by ring
      _ < 176 * (Real.exp (-100) / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right (by norm_num) hp
      _ = _ := by ring
  exact hstrict.trans_le (hsmall.trans hlarge)

/-- Ramare pages 119 and 120, negation of the printed auxiliary integral bound.
The witness is log x divided by R equal to 2500, not a Mangoldt counterexample. -/
theorem not_printed_auxiliary_integral_bound :
    ¬ ∀ a : ℝ, 2 * Real.log (2.44 * 10 ^ 12 : ℝ) ^ 2 ≤ a →
      (∫ u in Ioi (Real.log (2.44 * 10 ^ 12 : ℝ)),
        u * Real.exp (-a / u - u) / (2 * Real.pi)) ≤
      (1 + 2 * Real.sqrt a) / (2 * Real.pi) * Real.exp (-2 * Real.sqrt a) := by
  have hl0 : 0 < Real.log (2.44 * 10 ^ 12 : ℝ) := Real.log_pos (by norm_num)
  have hl : Real.log (2.44 * 10 ^ 12 : ℝ) ≤ 30 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc
      (2.44 * 10 ^ 12 : ℝ) ≤ (2.7 : ℝ) ^ 30 := by norm_num
      _ ≤ Real.exp 1 ^ 30 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq := pow_le_pow_left₀ hl0.le hl 2
  have htransition : 2 * Real.log (2.44 * 10 ^ 12 : ℝ) ^ 2 ≤ 2500 := by nlinarith
  have hbad := saddle_integral_exceeds_printed _ hl0 (by linarith)
  intro h
  have hh := h 2500 htransition
  have hsqrt : Real.sqrt (2500 : ℝ) = 50 := by norm_num
  rw [hsqrt] at hh
  norm_num [saddleKernel] at hbad hh
  exact (not_lt_of_ge hh) hbad

end LeanLab.ChirreHagen2025.Audit391b
