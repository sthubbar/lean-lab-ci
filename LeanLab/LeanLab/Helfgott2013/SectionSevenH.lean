/-
# Helfgott 2013, arXiv 1312.7748v2, Section 7.3, the constants C_{η+,0} and C_{η+,1}

Unit U-1121, T1 PROVE, P0001, run 20261019T2303Z-16260.

The paper, start of Section 7.3, read in Claude in Chrome on arxiv.org/html/1312.7748:
by (7.3) and (7.22), sup_{r ≥ t} η+(r) ≤ min(1.07996, 1.19073/t) for all t ≥ 0, so

  C_{η+,0} = 0.7131 ∫₀^∞ (sup_{r≥t} η+(r))²/√t dt
           ≤ 0.7131 (∫₀¹ 1.07996²/√t dt + ∫₁^∞ 1.19073²/t^{5/2} dt) ≤ 2.3375,
  C_{η+,1} ≤ 0.7131 ∫₁^∞ (log t/√t)(sup η+)² dt ≤ 0.7131 ∫₁^∞ 1.19073² log t/t^{5/2} dt ≤ 0.4494.

Before this unit the lab had only the arithmetic after these bounds, `E_coeffs`. Here the two
integral bounds are PROVED for ANY measurable `s` with the paper's pointwise bound, so they
apply to `s(t) = sup_{r ≥ t} η+(r)`. Values: 2.33743 against 2.3375, 0.449343 against 0.4494.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Helfgott2013.SectionSevenH

open Real MeasureTheory Set Filter Topology

/-- `∫₀¹ t^{−1/2} dt = 2`. -/
lemma int_rpow_half : ∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- `∫₁^∞ t^{−5/2} dt = 2/3`. -/
lemma int_rpow_five_half : ∫ t in Ioi (1 : ℝ), t ^ (-(5 / 2 : ℝ)) = 2 / 3 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- `∫₁^∞ log t · t^{−5/2} dt = 4/9`. -/
lemma int_log_rpow_five_half : ∫ t in Ioi (1 : ℝ), Real.log t * t ^ (-(5 / 2 : ℝ)) = 4 / 9 := by
  set F : ℝ → ℝ := fun t => -(2 / 3 * Real.log t + 4 / 9) * t ^ (-(3 / 2 : ℝ)) with hF
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt F (Real.log x * x ^ (-(5 / 2 : ℝ))) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    have h1 := (((Real.hasDerivAt_log hx0.ne').const_mul (2 / 3 : ℝ)).add_const (4 / 9 : ℝ)).neg
    have h2 := Real.hasDerivAt_rpow_const (x := x) (p := -(3 / 2 : ℝ)) (Or.inl hx0.ne')
    have e1 : x ^ (-(3 / 2 : ℝ) - 1) = x ^ (-(5 / 2 : ℝ)) := by norm_num
    have e2 : x ^ (-(5 / 2 : ℝ)) = x ^ (-(3 / 2 : ℝ)) * x⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]; norm_num
    convert h1.mul h2 using 1
    rw [e1, e2]
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 1) 1 :=
    (hderiv 2 (by norm_num) |>.continuousAt |> fun _ => by
      have : ContinuousAt F 1 := by
        have h1 : ContinuousAt (fun t : ℝ => Real.log t) 1 := Real.continuousAt_log one_ne_zero
        have h2 : ContinuousAt (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) 1 :=
          Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
        exact ((h1.const_mul _).add continuousAt_const).neg.mul h2
      exact this.continuousWithinAt)
  have hint : IntegrableOn (fun t => Real.log t * t ^ (-(5 / 2 : ℝ))) (Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) one_pos)
      ?_ ?_
    · exact (Real.measurable_log.mul (measurable_id.pow_const _)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : 0 < t := lt_trans one_pos ht1
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
      have e : t ^ (-(3 / 2 : ℝ)) = t * t ^ (-(5 / 2 : ℝ)) := by
        conv_lhs => rw [show (-(3 / 2 : ℝ)) = 1 + -(5 / 2) by norm_num]
        rw [Real.rpow_add ht0, Real.rpow_one]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e]
      exact mul_le_mul_of_nonneg_right hlog (by positivity)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_atTop (r := (3 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have := ((h1.const_mul (2 / 3 : ℝ)).add (h2.const_mul (4 / 9 : ℝ))).neg
    simp only [mul_zero, add_zero, neg_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [hF, Real.rpow_neg ht.le]
    field_simp
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [hF]

/-- **C_{η+,0} ≤ 2.3375.** For measurable `s` with `|s t| ≤ 1.07996` on `(0, 1]` and
`|s t| ≤ 1.19073/t` for `t > 1`: `0.7131 ∫₀^∞ s(t)² t^{−1/2} dt ≤ 2.3375`. -/
theorem C_etaPlus_0 (s : ℝ → ℝ) (hs : Measurable s)
    (h1 : ∀ t ∈ Ioc (0 : ℝ) 1, |s t| ≤ 1.07996) (h2 : ∀ t, 1 < t → |s t| ≤ 1.19073 / t) :
    0.7131 * ∫ t in Ioi (0 : ℝ), s t ^ 2 * t ^ (-(1 / 2 : ℝ)) ≤ 2.3375 := by
  have hmeas : AEStronglyMeasurable (fun t => s t ^ 2 * t ^ (-(1 / 2 : ℝ))) volume :=
    ((hs.pow_const 2).mul (measurable_id.pow_const _)).aestronglyMeasurable
  have b1 : ∀ t ∈ Ioc (0 : ℝ) 1, s t ^ 2 * t ^ (-(1 / 2 : ℝ)) ≤ 1.07996 ^ 2 * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have := h1 t ht
    have hsq : s t ^ 2 ≤ 1.07996 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg ht.1.le _)
  have b2 : ∀ t ∈ Ioi (1 : ℝ), s t ^ 2 * t ^ (-(1 / 2 : ℝ)) ≤ 1.19073 ^ 2 * t ^ (-(5 / 2 : ℝ)) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := lt_trans one_pos ht1
    have hsq : s t ^ 2 ≤ (1.19073 / t) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 t ht1) 2
    have e : t ^ (-(5 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) / t ^ 2 := by
      rw [show (-(5 / 2 : ℝ)) = -(1 / 2) - 2 by norm_num, Real.rpow_sub ht0, Real.rpow_two]
    rw [e]
    calc s t ^ 2 * t ^ (-(1 / 2 : ℝ)) ≤ (1.19073 / t) ^ 2 * t ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg ht0.le _)
      _ = 1.19073 ^ 2 * (t ^ (-(1 / 2 : ℝ)) / t ^ 2) := by ring
  have i1m : IntegrableOn (fun t : ℝ => 1.07996 ^ 2 * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
    refine Integrable.const_mul ?_ _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have i2m : IntegrableOn (fun t : ℝ => 1.19073 ^ 2 * t ^ (-(5 / 2 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  have i1 : IntegrableOn (fun t => s t ^ 2 * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
    refine Integrable.mono' i1m hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_nonneg ht.1.le (-(1 / 2 : ℝ)); positivity)]
    exact b1 t ht
  have i2 : IntegrableOn (fun t => s t ^ 2 * t ^ (-(1 / 2 : ℝ))) (Ioi 1) := by
    refine Integrable.mono' i2m hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_nonneg ht0.le (-(1 / 2 : ℝ)); positivity)]
    exact b2 t ht
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi i1 i2]
  have m1 := setIntegral_mono_on i1 i1m measurableSet_Ioc b1
  have m2 := setIntegral_mono_on i2 i2m measurableSet_Ioi b2
  rw [integral_const_mul, int_rpow_half] at m1
  rw [integral_const_mul, int_rpow_five_half] at m2
  nlinarith

/-- **C_{η+,1} ≤ 0.4494.** For measurable `s` with `|s t| ≤ 1.19073/t` for `t > 1`:
`0.7131 ∫₁^∞ log t · t^{−1/2} s(t)² dt ≤ 0.4494`. -/
theorem C_etaPlus_1 (s : ℝ → ℝ) (hs : Measurable s) (h2 : ∀ t, 1 < t → |s t| ≤ 1.19073 / t) :
    0.7131 * ∫ t in Ioi (1 : ℝ), Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2 ≤ 0.4494 := by
  have hmeas : AEStronglyMeasurable (fun t => Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2) volume :=
    ((Real.measurable_log.mul (measurable_id.pow_const _)).mul (hs.pow_const 2)).aestronglyMeasurable
  have b2 : ∀ t ∈ Ioi (1 : ℝ), Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2 ≤
      1.19073 ^ 2 * (Real.log t * t ^ (-(5 / 2 : ℝ))) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := lt_trans one_pos ht1
    have hsq : s t ^ 2 ≤ (1.19073 / t) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 t ht1) 2
    have e : t ^ (-(5 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) / t ^ 2 := by
      rw [show (-(5 / 2 : ℝ)) = -(1 / 2) - 2 by norm_num, Real.rpow_sub ht0, Real.rpow_two]
    have hpos : 0 ≤ Real.log t * t ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _)
    rw [e]
    calc Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2
        ≤ Real.log t * t ^ (-(1 / 2 : ℝ)) * (1.19073 / t) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hpos
      _ = 1.19073 ^ 2 * (Real.log t * (t ^ (-(1 / 2 : ℝ)) / t ^ 2)) := by ring
  have hlogint : IntegrableOn (fun t => Real.log t * t ^ (-(5 / 2 : ℝ))) (Ioi 1) := by
    by_contra hc
    have := int_log_rpow_five_half
    rw [integral_undef hc] at this
    norm_num at this
  have i2m : IntegrableOn (fun t : ℝ => 1.19073 ^ 2 * (Real.log t * t ^ (-(5 / 2 : ℝ)))) (Ioi 1) :=
    hlogint.const_mul _
  have i2 : IntegrableOn (fun t => Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2) (Ioi 1) := by
    refine Integrable.mono' i2m hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have : 0 ≤ Real.log t * t ^ (-(1 / 2 : ℝ)) * s t ^ 2 :=
      mul_nonneg (mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg this]
    exact b2 t ht
  have m2 := setIntegral_mono_on i2 i2m measurableSet_Ioi b2
  rw [integral_const_mul, int_log_rpow_five_half] at m2
  nlinarith

end LeanLab.Helfgott2013.SectionSevenH
