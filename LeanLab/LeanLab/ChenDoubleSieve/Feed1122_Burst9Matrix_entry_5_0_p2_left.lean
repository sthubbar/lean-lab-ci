import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_right
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit2

/-!
# Feed 1122, second split of `Burst9Matrix.entry_5_0`: the left half panel

Source: Wu 2004, arXiv 0705.1652, display 7.2, kernel Xi1 of display 3.21, page 14, row 6 of
Table 1, so `s = 27/10` and `sp = 347/100`. The two windows of display 3.21 start at
`sp - sp/s - 1 = 3199/2700` and `sp - 2 = 147/100`, both inside the left half panel `[1, 8/5]`,
so the half panel splits three ways: the `sigma0` term alone on `[1, 3199/2700]`, the `sigma0` term
plus the descending window on `[3199/2700, 147/100]`, and the `sigma0` term plus the `(t+1)^2`
window on `[147/100, 8/5]`. The `(t+1)^2` window is proved here; the `sigma0` quadrature on the
half panel and the descending window are the two LEAF pieces. The twenty certified panels
`b9_pan_0` to `b9_pan_19` of `Burst9MatrixCol0` give only `0.00210390606`, about `2.96e-8` below
the true value `0.00210393568`, which is more than the margin, so a finer quadrature is needed.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table LeanLab.ChenDoubleSieve.Wu04Functional
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_right

open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit2

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
integrated over the left half panel `[1, 8/5]` of `a_{6,1}`. High precision quadrature gives
`0.0021039356802`, so the stated bound leaves `9.1e-9`. The forty midpoint panels of width
`3/200` on `[1, 8/5]`, twice as fine as `b9_pan_0` to `b9_pan_19`, would lose about `7.4e-9`.
HARD. -/
theorem leaf_sigma_left :
    (0.0021039266 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hI : IntervalIntegrable (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) volume
      (1 : ℝ) (8/5 : ℝ) :=
    sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num)
  exact hI

/-- LEAF: Wu 2004 display 7.2, the descending window of the kernel Xi1 of display 3.21, page 14,
for `s = 27/10`, `sp = 347/100`, on `[sp - sp/s - 1, sp - 2] = [3199/2700, 147/100]`.
High precision quadrature gives `0.0189919674730`, so the stated bound leaves `4.7e-10`. It splits
into `log (t+1)/t`, a `log (17/10)` term and `log (247/100 - t)/(2t)`, as `c4_J3_eq` does for
row 5. MEDIUM. -/
theorem leaf_W3 :
    (0.018991967 : ℝ) ≤ ∫ t in (3199/2700 : ℝ)..(147/100 : ℝ),
      log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (3199/2700 : ℝ) (147/100 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (3199/2700 : ℝ) (147/100 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => log (247/100 - t) / (2 * t)) volume
      (3199/2700 : ℝ) (147/100 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_id) ?_
      intro t ht
      have h2 : (0 : ℝ) < 247/100 - t := by linarith [ht.2]
      exact ne_of_gt h2
    · intro t ht
      have h2 : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have hpt : ∀ t ∈ uIcc (3199/2700 : ℝ) (147/100),
      log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t) =
        (1/2) * (log (t + 1) / t) - (1/2) * log (17/10) * (1 / t) -
          log (247/100 - t) / (2 * t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have h1 : (0 : ℝ) < t + 1 := by linarith
    have h3 : (0 : ℝ) < 247/100 - t := by linarith [ht.2]
    have hden : ((17/10) * (247/100 - t) : ℝ) ≠ 0 := by positivity
    rw [Real.log_div (ne_of_gt h1) hden,
      Real.log_mul (by norm_num : (17/10 : ℝ) ≠ 0) (ne_of_gt h3)]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub
      ((hI1.const_mul (1/2)).sub (hI2.const_mul (1/2 * log (17/10)))) hI3]
  rw [intervalIntegral.integral_sub (hI1.const_mul (1/2)) (hI2.const_mul (1/2 * log (17/10)))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((147/100 : ℝ) / (3199/2700)) = (3969/3199 : ℝ) by norm_num]
  have hL := w3_L_lower
  have hU := w3_U_upper
  have h17 := w3_log_17
  have hba := w3_log_ba
  have hprod : log (17/10 : ℝ) * log (3969/3199 : ℝ) ≤
      (0.530628251062171 : ℝ) * (0.215675912833548 : ℝ) :=
    mul_le_mul h17 hba.2 (le_trans (by norm_num) hba.1) (by norm_num)
  have hprod' : (1/2 : ℝ) * log (17/10) * log (3969/3199) =
      (1/2) * (log (17/10 : ℝ) * log (3969/3199 : ℝ)) := by ring
  rw [hprod']
  linarith [hL, hU, hprod]

/-- `log (507/400)` two-sided, `x = 107/907`, eight terms. -/
theorem l5_log_507_400 : (0.23704645648320 : ℝ) ≤ log (507/400 : ℝ) ∧
    log (507/400 : ℝ) ≤ (0.23704645648321 : ℝ) := by
  have h := log_enclosure (y := (507/400 : ℝ)) (x := (107/907 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (160/147)` two-sided, `x = 13/307`, six terms. -/
theorem l5_log_160_147 : (0.08474122845509 : ℝ) ≤ log (160/147 : ℝ) ∧
    log (160/147 : ℝ) ≤ (0.08474122845510 : ℝ) := by
  have h := log_enclosure (y := (160/147 : ℝ)) (x := (13/307 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 6
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `∫_{147/100}^{8/5} log (t+1)/t`, from the `log (t+1)` series at `307/200` with eight terms,
radius `1/39`. -/
theorem l5_L_lower :
    (0.0787857708 : ℝ) ≤ ∫ t in (147/100 : ℝ)..(8/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (147/100 : ℝ) (8/5), |(307/200 - t) / (307/200 + 1)| ≤ 1/39 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(307/200 : ℝ) - t| ≤ 13/200 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (307/200 : ℝ) + 1 = 507/200 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 307/200 + 1), hden]
    have h3 : |(307/200 : ℝ) - t| / (507/200) ≤ (13/200) / (507/200) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (13/200 : ℝ) / (507/200) = 1/39 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := 147/100) (b := 8/5) (c := 307/200) (r := 1/39)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  simp only [Finset.sum_range_succ] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (147/100 : ℝ)..(8/5 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (147/100 : ℝ)..(8/5 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have h2lo : (0.69314718055 : ℝ) ≤ log 2 := log_two_bounds.1
  have hl := l5_log_160_147
  have h5 := l5_log_507_400
  have h507 : log (507/200 : ℝ) = log 2 + log (507/400) := by
    rw [show (507/200 : ℝ) = 2 * (507/400) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h507lo : (0.69314718055 + 0.23704645648320 : ℝ) ≤ log (507/200) := by
    rw [h507]; linarith [h5.1]
  have hprod : ((0.69314718055 + 0.23704645648320 : ℝ) * 0.08474122845509) ≤
      log (507/200) * log (160/147) := by
    refine mul_le_mul h507lo hl.1 (by norm_num) ?_
    linarith [h507lo]
  linarith [h, hprod, hl.1, hl.2]

/-- The `(t+1)^2` window on `[147/100, 8/5]`, split into `log (t+1)` and `log (4199/1000)`. -/
theorem l5_J2_eq :
    (∫ t in (147/100 : ℝ)..(8/5 : ℝ), log ((t + 1) ^ 2 / (4199/1000)) / (2 * t)) =
      (∫ t in (147/100 : ℝ)..(8/5 : ℝ), log (t + 1) / t) -
        (1/2) * log (4199/1000) * log (160/147) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (147/100 : ℝ) (8/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (147/100 : ℝ) (8/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (147/100 : ℝ) (8/5),
      log ((t + 1) ^ 2 / (4199/1000)) / (2 * t) =
        log (t + 1) / t - (1/2) * log (4199/1000) * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have hnum : ((t + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hnum (by norm_num : (4199/1000 : ℝ) ≠ 0), Real.log_pow]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1/2 * log (4199/1000)))]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((8/5 : ℝ) / (147/100)) = (160/147 : ℝ) by norm_num]

/-- The `(t+1)^2` window of display 3.21 on `[147/100, 8/5]`, certified. -/
theorem l5_W2_lower :
    (0.017990447 : ℝ) ≤ ∫ t in (147/100 : ℝ)..(8/5 : ℝ), log ((t + 1) ^ 2 / (4199/1000)) / (2 * t) := by
  rw [l5_J2_eq]
  have hL := l5_L_lower
  have h2hi : log 2 ≤ (0.69314718056 : ℝ) := log_two_bounds.2
  have hq := r5_log_4199_4000
  have hl := l5_log_160_147
  have hPhi : log (4199/1000) ≤ (2 * 0.69314718056 + 0.04855204058217 : ℝ) := by
    rw [r5_log_P]; linarith [hq.2]
  have hw : log (4199/1000) * log (160/147) ≤
      (2 * 0.69314718056 + 0.04855204058217 : ℝ) * 0.08474122845510 :=
    mul_le_mul hPhi hl.2 (le_trans (by norm_num) hl.1) (by norm_num)
  linarith [hL, hw]

/-- On `(1, 11/5)` the row-6 kernel is the `sigma0` term plus its two windows. -/
theorem l5_xi1_eq {t : ℝ} (ht : t ∈ Set.uIoo (1 : ℝ) (11/5)) :
    Wu04Functional.Xi1 (27/10) (347/100) t =
      log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
        Wu04Functional.ind (147/100) 3 t * (log ((t + 1) ^ 2 / (4199/1000)) / (2 * t)) +
        Wu04Functional.ind (3199/2700) (147/100) t *
          (log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t)) := by
  unfold Wu04Functional.Xi1
  have hA : ((27/10 : ℝ) - 1) * (347/100 - 1) = 4199/1000 := by norm_num
  have hB : (16 : ℝ) / (4199/1000) = 16000/4199 := by norm_num
  have hC : (347/100 : ℝ) - 2 = 147/100 := by norm_num
  have hD : (347/100 : ℝ) - 347/100/(27/10) - 1 = 3199/2700 := by norm_num
  have hE : (27/10 : ℝ) - 1 = 17/10 := by norm_num
  have hF : (347/100 : ℝ) - 1 = 247/100 := by norm_num
  rw [hA, hB, hC, hD, hE, hF]
  ring

/-- The left half panel of `a_{6,1}` in Wu's display 7.2 from the two LEAF pieces and the
certified `(t+1)^2` window: the stated bound of `Feed1122_Burst9Matrix_entry_5_0.leaf_left`. -/
theorem left_half_of_leaves :
    (9949228577/250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), tableKernel 5 t := by
  have he : (∫ t in (1 : ℝ)..(8/5 : ℝ), tableKernel 5 t) =
      ∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t := by
    simp only [Wu04Table.tableKernel, Wu04Functional.grid, Wu04Functional.tableSp]
    norm_num
  rw [he]
  have hin : ∀ {a b : ℝ}, 1 ≤ a → b ≤ 8/5 → ∀ t ∈ Set.uIoo a b, a ≤ b →
      t ∈ Set.uIoo (1 : ℝ) (11/5) := by
    intro a b ha hb t ht hab
    rw [Set.uIoo, min_eq_left hab, max_eq_right hab] at ht
    rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hS1 : ∀ t ∈ Set.uIoo (1 : ℝ) (3199/2700),
      log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) =
        Wu04Functional.Xi1 (27/10) (347/100) t := by
    intro t ht
    rw [l5_xi1_eq (hin (le_refl _) (by norm_num) t ht (by norm_num))]
    rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 3199/2700),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 3199/2700)] at ht
    have e1 : Wu04Functional.ind (147/100) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (3199/2700) (147/100) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    rw [e1, e2]
    ring
  have hS2 : ∀ t ∈ Set.uIoo (3199/2700 : ℝ) (147/100),
      (log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t)) =
        Wu04Functional.Xi1 (27/10) (347/100) t := by
    intro t ht
    rw [l5_xi1_eq (hin (by norm_num) (by norm_num) t ht (by norm_num))]
    rw [Set.uIoo, min_eq_left (by norm_num : (3199/2700 : ℝ) ≤ 147/100),
      max_eq_right (by norm_num : (3199/2700 : ℝ) ≤ 147/100)] at ht
    have e1 : Wu04Functional.ind (147/100) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (3199/2700) (147/100) t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [e1, e2]
    ring
  have hS3 : ∀ t ∈ Set.uIoo (147/100 : ℝ) (8/5),
      (log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) ^ 2 / (4199/1000)) / (2 * t)) =
        Wu04Functional.Xi1 (27/10) (347/100) t := by
    intro t ht
    rw [l5_xi1_eq (hin (by norm_num) (le_refl _) t ht (by norm_num))]
    rw [Set.uIoo, min_eq_left (by norm_num : (147/100 : ℝ) ≤ 8/5),
      max_eq_right (by norm_num : (147/100 : ℝ) ≤ 8/5)] at ht
    have e1 : Wu04Functional.ind (147/100) 3 t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, by linarith [ht.2]⟩
    have e2 : Wu04Functional.ind (3199/2700) (147/100) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨-, h2⟩; linarith [ht.1])
    rw [e1, e2]
    ring
  have hJ3int : IntervalIntegrable (fun t : ℝ => log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t))
      volume (3199/2700 : ℝ) (147/100) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · refine ContinuousOn.div (continuousOn_id.add continuousOn_const) ?_ ?_
        · exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
        · intro t ht
          have h4 : (0 : ℝ) < 247/100 - t := by linarith [ht.2]
          exact ne_of_gt (by positivity)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        have h6 : (0 : ℝ) < 247/100 - t := by linarith [ht.2]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hJ2int : IntervalIntegrable (fun t : ℝ => log ((t + 1) ^ 2 / (4199/1000)) / (2 * t))
      volume (147/100 : ℝ) (8/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_id.add continuousOn_const).pow 2 |>.div_const (4199/1000)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hs1 := sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (3199/2700 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hs2 := sigma0_div_two_integrable_Icc (a := (3199/2700 : ℝ)) (b := (147/100 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hs3 := sigma0_div_two_integrable_Icc (a := (147/100 : ℝ)) (b := (8/5 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hI1 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (27/10) (347/100) t) volume
      (1 : ℝ) (3199/2700) := (hs1.const_mul (log (16000/4199))).congr_uIoo hS1
  have hI2 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (27/10) (347/100) t) volume
      (3199/2700 : ℝ) (147/100) := ((hs2.const_mul (log (16000/4199))).add hJ3int).congr_uIoo hS2
  have hI3 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (27/10) (347/100) t) volume
      (147/100 : ℝ) (8/5) := ((hs3.const_mul (log (16000/4199))).add hJ2int).congr_uIoo hS3
  have h12 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have h123 := intervalIntegral.integral_add_adjacent_intervals (hI1.trans hI2) hI3
  have e1 : (∫ t in (1 : ℝ)..(3199/2700 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t) =
      log (16000/4199) * (∫ t in (1 : ℝ)..(3199/2700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (27/10) (347/100) t)
      (g := fun t : ℝ => log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)))
      (fun t ht => (hS1 t ht).symm)]
    rw [intervalIntegral.integral_const_mul]
  have e2 : (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t) =
      log (16000/4199) * (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ),
          log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (27/10) (347/100) t)
      (g := fun t : ℝ => log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) / ((17/10) * (247/100 - t))) / (2 * t))
      (fun t ht => (hS2 t ht).symm)]
    rw [intervalIntegral.integral_add (hs2.const_mul (log (16000/4199))) hJ3int]
    rw [intervalIntegral.integral_const_mul]
  have e3 : (∫ t in (147/100 : ℝ)..(8/5 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t) =
      log (16000/4199) * (∫ t in (147/100 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (147/100 : ℝ)..(8/5 : ℝ), log ((t + 1) ^ 2 / (4199/1000)) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (27/10) (347/100) t)
      (g := fun t : ℝ => log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) ^ 2 / (4199/1000)) / (2 * t))
      (fun t ht => (hS3 t ht).symm)]
    rw [intervalIntegral.integral_add (hs3.const_mul (log (16000/4199))) hJ2int]
    rw [intervalIntegral.integral_const_mul]
  have hs12 := intervalIntegral.integral_add_adjacent_intervals hs1 hs2
  have hs123 := intervalIntegral.integral_add_adjacent_intervals (hs1.trans hs2) hs3
  have hsig := leaf_sigma_left
  have hW3 := leaf_W3
  have hW2 := l5_W2_lower
  have h2lo : (0.69314718055 : ℝ) ≤ log 2 := log_two_bounds.1
  have hq := r5_log_4199_4000
  have hclo : (2 * 0.69314718055 - 0.04855204058217 : ℝ) ≤ log (16000/4199) := by
    rw [r5_log_c]; linarith [hq.2]
  have hsum : (∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(3199/2700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (147/100 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    linarith [hs12, hs123]
  have hmul : (2 * 0.69314718055 - 0.04855204058217 : ℝ) * 0.0021039266 ≤
      log (16000/4199) * (∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    refine mul_le_mul hclo hsig (by norm_num) ?_
    linarith [hclo]
  have hdist : log (16000/4199) * (∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      log (16000/4199) * (∫ t in (1 : ℝ)..(3199/2700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (16000/4199) * (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (16000/4199) * (∫ t in (147/100 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    rw [hsum]; ring
  linarith [h12, h123, e1, e2, e3, hmul, hdist, hW3, hW2]

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left
