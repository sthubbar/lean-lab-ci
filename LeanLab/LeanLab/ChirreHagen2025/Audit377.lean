import LeanLab.ChirreHagen2025.Additional122

/-!
Audit of the numerical integral expression on P0075 page 14.
https://arxiv.org/abs/2512.23534
The numerical mismatch is a QUESTION. It does not refute Lemma A.2.
AI wrote this Lean code. Goldbach is open.
-/
open MeasureTheory Filter
namespace LeanLab.ChirreHagen2025.Audit377

/-- P0075 page 14, the elementary error-integral antiderivative numerator. -/
noncomputable def errorPrimitive (x : ℝ) : ℝ :=
  (2 * Real.log x ^ 3 + 10 * Real.log x ^ 2 + 40 * Real.log x + 80) / Real.sqrt x

/-- P0075 page 14, the constant obtained from its displayed improper integral. -/
noncomputable def displayedConstant : ℝ :=
  Real.log 2 ^ 2 / 2 - Real.log 3 * Real.log 2 / 3 + Real.log 3 -
    Real.log 3 ^ 2 / 2 + errorPrimitive 3 / (8 * Real.pi)

/-- P0075 page 14, derivative check for the displayed elementary error kernel. -/
theorem errorPrimitive_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt errorPrimitive
      (-((Real.log x - 1) * Real.log x ^ 2 / (x * Real.sqrt x))) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hp := (((hl.pow 3).const_mul 2).add ((hl.pow 2).const_mul 10)).add
    ((hl.const_mul 40).add_const 80)
  have h := hp.div hs (Real.sqrt_ne_zero'.mpr hx)
  convert h using 1
  · ext y
    simp only [errorPrimitive, Pi.add_apply, Pi.div_apply, Pi.pow_apply]
    ring
  · simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply,
      Nat.reduceSub, Nat.cast_ofNat, pow_one]
    have hr : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    field_simp
    rw [Real.sq_sqrt hx.le]
    ring

/-- P0075 page 14, vanishing boundary term for the error integral. -/
theorem errorPrimitive_tendsto :
    Filter.Tendsto errorPrimitive Filter.atTop (nhds 0) := by
  have hl (n : ℕ) : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ n / Real.sqrt x) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (n : ℝ)
        (by norm_num)).tendsto_div_nhds_zero
  have h := (((hl 3).const_mul 2).add ((hl 2).const_mul 10)).add
    (((hl 1).const_mul 40).add ((hl 0).const_mul 80))
  convert h using 1
  · ext x
    simp only [errorPrimitive, pow_zero, pow_one]
    ring
  · norm_num

/-- P0075 page 14, exact evaluation of the displayed error integral. -/
theorem error_integral :
    (∫ y in Set.Ioi (3 : ℝ),
      (Real.log y - 1) * Real.log y ^ 2 / (y * Real.sqrt y)) = errorPrimitive 3 := by
  have hd (x : ℝ) (hx : x ∈ Set.Ici (3 : ℝ)) :=
    (errorPrimitive_hasDerivAt x (by have hx3 : 3 ≤ x := hx; linarith)).neg
  have hn (x : ℝ) (hx : x ∈ Set.Ici (3 : ℝ)) :
      0 ≤ (Real.log x - 1) * Real.log x ^ 2 / (x * Real.sqrt x) := by
    have hx3 : (3 : ℝ) ≤ x := hx
    have hx0 : 0 < x := by linarith
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx
    have h3 := Real.log_three_gt_d9
    apply div_nonneg
    · apply mul_nonneg (by linarith) (sq_nonneg _)
    · positivity
  have ht := errorPrimitive_tendsto.neg
  simpa only [Pi.neg_apply, neg_neg, neg_zero, zero_sub] using
    integral_Ioi_of_hasDerivAt_of_nonneg' hd
      (fun x hx => by rw [neg_neg]; exact hn x (show 3 ≤ x from le_of_lt (show 3 < x from hx))) ht

/-- P0075 page 14, a rational lower bound for the printed constant expression.
This records a numerical QUESTION about 3.5401, not a theorem refutation. -/
theorem displayedConstant_gt : 3.6 < displayedConstant := by
  have h2lo : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 ≤ (0.70 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h3lo : (1.09 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have h3hi : Real.log 3 ≤ (1.10 : ℝ) := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hshi : Real.sqrt 3 ≤ (1.733 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hq : (138 : ℝ) ≤
      2 * Real.log 3 ^ 3 + 10 * Real.log 3 ^ 2 + 40 * Real.log 3 + 80 := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.09) h3lo 2
    have hcu := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.09) h3lo 3
    nlinarith
  have hden : 0 < Real.sqrt 3 * (8 * Real.pi) := by positivity
  have hdenhi : Real.sqrt 3 * (8 * Real.pi) ≤ 44 := by
    have hp := Real.pi_lt_d2.le
    nlinarith [mul_le_mul hshi hp (le_of_lt Real.pi_pos) (by norm_num : (0 : ℝ) ≤ 1.733)]
  have htail : (138 / 44 : ℝ) ≤ errorPrimitive 3 / (8 * Real.pi) := by
    unfold errorPrimitive
    rw [div_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have h22 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.69) h2lo 2
  have h33 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 3) h3hi 2
  have h23 : Real.log 3 * Real.log 2 ≤ (1.10 : ℝ) * 0.70 :=
    mul_le_mul h3hi h2hi (by linarith) (by norm_num)
  unfold displayedConstant
  nlinarith

/-- P0075 page 14, evaluation with exactly the displayed error integrand. -/
theorem printed_error_integral :
    (∫ y in Set.Ioi (3 : ℝ),
      ((Real.log y - 1) / y ^ 2) * (Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi))) =
        errorPrimitive 3 / (8 * Real.pi) := by
  calc
    _ = ∫ y in Set.Ioi (3 : ℝ),
        ((Real.log y - 1) * Real.log y ^ 2 / (y * Real.sqrt y)) / (8 * Real.pi) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := by have : 3 < y := hy; linarith
      have hr : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy0).ne'
      field_simp
      rw [Real.sq_sqrt hy0.le]
    _ = _ := by rw [integral_div, error_integral]

/-- P0075 page 14, QUESTION about its printed final numerical inequality.
The exact displayed left side is larger than 3.6. Lemma A.2 is not refuted. -/
theorem printed_expression_gt :
    3.6 < Real.log 2 ^ 2 / 2 - Real.log 3 * Real.log 2 / 3 + Real.log 3 -
      Real.log 3 ^ 2 / 2 +
        (∫ y in Set.Ioi (3 : ℝ),
          ((Real.log y - 1) / y ^ 2) * (Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi))) := by
  rw [printed_error_integral]
  exact displayedConstant_gt

/-- P0075 page 14, lab variant using the finite primes below six.
This is only the scalar constant of the alternate finite Abel split. -/
noncomputable def cutoffSixConstant : ℝ :=
  Real.log 2 ^ 2 / 2 + Real.log 3 ^ 2 / 3 + Real.log 5 ^ 2 / 5 -
    Real.log 6 * (Real.log 2 + Real.log 3 + Real.log 5) / 6 +
    Real.log 6 - Real.log 6 ^ 2 / 2 + errorPrimitive 6 / (8 * Real.pi)

/-- P0075 page 14, arithmetic repair route with a split at six.
This asserts no prime sum bound and changes no existing target statement. -/
theorem cutoffSixConstant_lt : cutoffSixConstant < 3.536 := by
  have h2lo : (0.693 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 ≤ (0.694 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h3lo : (1.098 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have h3hi : Real.log 3 ≤ (1.099 : ℝ) := by linarith [Real.log_three_lt_d9]
  have he5 : Real.log (5 : ℝ) = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    rw [show (5 : ℝ) = (2 : ℝ) ^ 2 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h5lo : (1.586 : ℝ) ≤ Real.log 5 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h
    linarith
  have h5hi : Real.log 5 ≤ (1.637 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h
    have hh := Real.log_two_lt_d9
    linarith
  have he6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h6lo : (1.791 : ℝ) ≤ Real.log 6 := by linarith
  have h6hi : Real.log 6 ≤ (1.793 : ℝ) := by linarith
  have hsq6 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 6) h6hi 2
  have hcu6 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 6) h6hi 3
  have hq : 2 * Real.log 6 ^ 3 + 10 * Real.log 6 ^ 2 + 40 * Real.log 6 + 80 ≤
      (195.397 : ℝ) := by nlinarith
  have hs : (2.449 : ℝ) ≤ Real.sqrt 6 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hd : (8 * 3.1415 * 2.449 : ℝ) ≤ Real.sqrt 6 * (8 * Real.pi) := by
    have h := mul_le_mul hs Real.pi_gt_d4.le (by norm_num : (0 : ℝ) ≤ 3.1415)
      (Real.sqrt_nonneg 6)
    nlinarith
  have htail : errorPrimitive 6 / (8 * Real.pi) ≤ (3.175 : ℝ) := by
    unfold errorPrimitive
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 6 * (8 * Real.pi))).mpr
    nlinarith
  have h22 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 2) h2hi 2
  have h33 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 3) h3hi 2
  have h55 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 5) h5hi 2
  have h66 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.791) h6lo 2
  have hm : (1.791 * (0.693 + 1.098 + 1.586) : ℝ) ≤
      Real.log 6 * (Real.log 2 + Real.log 3 + Real.log 5) :=
    mul_le_mul h6lo (by linarith) (by norm_num) (by linarith)
  unfold cutoffSixConstant
  nlinarith

/-- P0075 page 14, QUESTION about the final claimed increment of 0.0001.
At the stated threshold the displayed boundary term exceeds that increment.
This scalar observation does not refute Lemma A.2. -/
theorem boundary_at_threshold_gt :
    (0.0001 : ℝ) < Real.log (10 ^ 13 : ℝ) ^ 3 /
      (8 * Real.pi * Real.sqrt (10 ^ 13 : ℝ)) := by
  have hl : (27 : ℝ) ≤ Real.log (10 ^ 13 : ℝ) := by
    calc
      (27 : ℝ) ≤ 39 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      _ = Real.log ((2 : ℝ) ^ 39) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (10 ^ 13 : ℝ) := Real.log_le_log (by positivity) (by norm_num)
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27) hl 3
  have hs : Real.sqrt (10 ^ 13 : ℝ) ≤ 4 * 10 ^ 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 ^ 13)]
  have hd : 8 * Real.pi * Real.sqrt (10 ^ 13 : ℝ) ≤ (128 * 10 ^ 6 : ℝ) := by
    have h := mul_le_mul Real.pi_lt_four.le hs (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  apply (lt_div_iff₀ (by positivity : 0 < 8 * Real.pi * Real.sqrt (10 ^ 13 : ℝ))).mpr
  have hu : (0.0001 : ℝ) * (8 * Real.pi * Real.sqrt (10 ^ 13 : ℝ)) ≤ 12800 := by
    calc
      _ ≤ (0.0001 : ℝ) * (128 * 10 ^ 6) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = 12800 := by norm_num
  exact lt_of_le_of_lt hu (lt_of_lt_of_le (by norm_num) hcube)

end LeanLab.ChirreHagen2025.Audit377
