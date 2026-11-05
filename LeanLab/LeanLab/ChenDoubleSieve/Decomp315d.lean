import LeanLab.ChenDoubleSieve.Decomp275i

/-!
Supply split for Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Split the upper sieve coefficient at three using both known local formulas.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem upper_weighted_split {F f : ℝ → ℝ} (h : IsLinearSieve F f)
    {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    4 / exp eulerMascheroniConstant *
      (∫ t in a..5, F t / (1 - t / 6)) =
    8 * (∫ t in a..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  have hFi : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : a ≤ 5)]
    refine (h.1.mono (fun t ht => ?_)).div (by fun_prop) ?_
    · change 0 < t
      linarith [ht.1]
    · intro t ht
      linarith [ht.2]
  have hi₁ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume a 3 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le ha3, Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_right (by norm_num)
  have hi₂ : IntervalIntegrable (fun t => F t / (1 - t / 6)) volume 3 5 := by
    apply hFi.mono_set
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5),
      Set.uIcc_of_le (by linarith : a ≤ 5)]
    exact Set.Icc_subset_Icc_left ha3
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, mul_add]
  have hsmall : (∫ t in a..3, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in a..3, 1 / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    dsimp only
    rw [Task275.linear_upper_three h (by linarith [ht.1]) ht.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlarge : (∫ t in (3 : ℝ)..5, F t / (1 - t / 6)) =
      (2 * exp eulerMascheroniConstant) * ∫ t in (3 : ℝ)..5,
        (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at ht
    dsimp only
    rw [Task275.linear_upper_five h ht]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsmall, hlarge]
  field_simp [Real.exp_ne_zero]
  <;> ring

/-- The actual F2 coefficient has an elementary split at the sieve transition.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 =
    8 * (∫ t in (258 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma1, show (1 / 2 - 41 / 125 : ℝ) / (1 / 12) = 258 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 258 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The actual F3 coefficient shares the same upper tail as F2.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F3_elementary {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 3 =
    8 * (∫ t in (327 / 125 : ℝ)..3, 1 / (t * (1 - t / 6))) +
    8 * (∫ t in (3 : ℝ)..5,
      (1 + ∫ x in (2 : ℝ)..(t - 1), log (x - 1) / x) / (t * (1 - t / 6))) := by
  change 4 / exp eulerMascheroniConstant *
    (∫ t in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t)) = _
  norm_num only [kappa1, sigma2, show (1 / 2 - 141 / 500 : ℝ) / (1 / 12) = 327 / 125 by norm_num,
    show (1 / 2 - 1 / 12 : ℝ) / (1 / 12) = 5 by norm_num]
  convert upper_weighted_split h (a := 327 / 125) (by norm_num) (by norm_num) using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- The elementary part of F2 and F3 has an exact logarithmic antiderivative.
Source: page 39 equation 10.4, derived integration helper. -/
theorem reciprocal_head {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    (∫ t in a..3, 1 / (t * (1 - t / 6))) = log ((6 - a) / a) := by
  have hcont₁ : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    linarith [ht.1]
  have hcont₂ : ContinuousOn (fun t : ℝ => (1 : ℝ) / (6 - t)) (Set.uIcc a 3) := by
    rw [Set.uIcc_of_le ha3]
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    linarith [ht.2]
  have he : (∫ t in a..3, 1 / (t * (1 - t / 6))) =
      (∫ t in a..3, 1 / t) + ∫ t in a..3, 1 / (6 - t) := by
    rw [← intervalIntegral.integral_add hcont₁.intervalIntegrable hcont₂.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha3] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht6 : 6 - t ≠ 0 := by linarith [ht.2]
    have htden : 1 - t / 6 ≠ 0 := by linarith [ht.2]
    field_simp [ht0, ht6, htden]
    <;> ring
  rw [he]
  simp only [one_div]
  rw [integral_inv_of_pos ha (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 6]
  norm_num only [show (6 - 3 : ℝ) = 3 by norm_num]
  rw [integral_inv_of_pos (by norm_num) (by linarith : 0 < 6 - a),
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by linarith : 6 - a ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div (by linarith : 6 - a ≠ 0) ha.ne']
  ring

/-- F2 and F3 differ only by an elementary logarithmic head.
CONDITIONAL ON IsLinearSieve. Source: page 39 equation 10.4. -/
theorem F2_sub_F3 {F f : ℝ → ℝ} (h : IsLinearSieve F f) (ω : ℝ → ℝ) :
    integralTerms F f ω 2 - integralTerms F f ω 3 =
      8 * (log (82 / 43 : ℝ) - log (141 / 109 : ℝ)) := by
  rw [F2_elementary h ω, F3_elementary h ω,
    reciprocal_head (a := 258 / 125) (by norm_num) (by norm_num),
    reciprocal_head (a := 327 / 125) (by norm_num) (by norm_num)]
  norm_num only [show (6 - 258 / 125 : ℝ) / (258 / 125) = 82 / 43 by norm_num,
    show (6 - 327 / 125 : ℝ) / (327 / 125) = 141 / 109 by norm_num]
  ring

/-- LEAF. Wu 2004 page 42 final numerical display, F0.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    13.473613 ≤ integralTerms F f ω 0 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F1.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 1 ≤ 3.891854 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F2.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 2 ≤ 20.432098 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F3.
The single actual integral coefficient satisfies its printed upper bound. -/
theorem numerical_F3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 3 ≤ 17.327241 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F4.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    0.697375 ≤ integralTerms F f ω 4 := by
  sorry

/-- LEAF. Wu 2004 page 42 final numerical display, F5.
The single actual integral coefficient satisfies its printed lower bound. -/
theorem numerical_F5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    2.118119 ≤ integralTerms F f ω 5 := by
  sorry

end LeanLab.ChenDoubleSieve.Task315
