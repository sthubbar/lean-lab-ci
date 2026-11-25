import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit

/-!
# Feed 1122, second split of `Burst9Matrix.entry_5_0`: the descending window kit

Source: Wu 2004, arXiv 0705.1652, display 7.2, kernel Xi1 of display 3.21, page 14.
The three lemmas `integral_pow_sub_div`, `log_affine_le_series` and `integral_log_affine_upper`
are verbatim copies of the private lemmas of the same names in
`LeanLab.ChenDoubleSieve.Burst9MatrixCol0`, lines 6991 to 7154, with `private` dropped and a new
namespace. The copy exists because `Burst9MatrixCol0` as one module goes over the 8 GB build
cap, so it cannot be imported; the proofs are unchanged. The `w3_` lemmas after them are new and
bound the two integrals of the descending window of row 6 of Table 1.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit2
open Wu04Table
open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LeanLab.ChenDoubleSieve.Wu04Integral LeanLab.ChenDoubleSieve.Wu04Functional
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit

/-- Exact value of `∫ (t-m)^k / t`: the binomial expansion of `integral_sub_pow_div`, with the
sign of `(t-m)^k = (-1)^k (m-t)^k` carried out front. -/
theorem integral_pow_sub_div {a b m : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    (∫ t in a..b, (t - m) ^ k / t) =
      (-1) ^ k * (m ^ k * log (b / a) + ∑ j ∈ Finset.range k,
        (-1) ^ (j + k) * m ^ j * (k.choose j : ℝ) *
          ((b ^ (k - j) - a ^ (k - j)) / ((k : ℝ) - j))) := by
  rw [← integral_sub_pow_div (a := a) (b := b) (c := m) (m := k) ha hab]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have h1 : ((-1 : ℝ) ^ k) * ((m - t) ^ k) = (t - m) ^ k := by
    rw [← mul_pow, show ((-1 : ℝ) * (m - t)) = t - m by ring]
  rw [← mul_div_assoc, h1]

/-! ### The `j = 0` panel of the `Xi1` rows

Rows 4-8 carry, on the middle piece of `[1, 11/5]`, the window `log ((t+1)/((s-1)(sp-1-t))): a
logarithm of a *decreasing* affine, with a minus sign in front of its integral.  The file's series
machinery only handles `log (t+1)`; here is the decreasing-argument version: expand `log (1 - u)`
with `u = (t - m)/(al - m)` by `Real.abs_log_sub_add_sum_range_le` around the midpoint `m` of the
piece, integrate the resulting polynomial against `1/(2t)` in closed form
(`integral_sub_pow_div`), and keep the alternating remainder. -/

/-- Pointwise upper bound for `log (al - t)` from the alternating series around `m`. -/
theorem log_affine_le_series {al m r t : ℝ} (hD : 0 < al - m) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : |(t - m) / (al - m)| ≤ r) (n : ℕ) :
    log (al - t) ≤ log (al - m) -
      (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r) := by
  have hx1 : |(t - m) / (al - m)| < 1 := lt_of_le_of_lt ht hr1
  have hS := Real.abs_log_sub_add_sum_range_le hx1 n
  have hb : |(t - m) / (al - m)| ^ (n + 1) / (1 - |(t - m) / (al - m)|) ≤
      r ^ (n + 1) / (1 - r) := by
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) ht _)
      (by linarith) (by linarith)
  have hle : log (1 - (t - m) / (al - m)) ≤
      -(∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
        r ^ (n + 1) / (1 - r) := by
    have h2 := (abs_le.mp (le_trans hS hb)).2
    linarith
  have h2 : (0 : ℝ) < 1 - (t - m) / (al - m) := by
    have h3 := (abs_lt.mp hx1).2
    linarith
  have harg : al - t = (al - m) * (1 - (t - m) / (al - m)) := by
    field_simp
    ring
  have hlog : log (al - t) = log (al - m) + log (1 - (t - m) / (al - m)) := by
    rw [harg, Real.log_mul (ne_of_gt hD) (ne_of_gt h2)]
  linarith

/-- `∫_a^b log (al - t)/(2t)` from above: the alternating series around `m`, integrated exactly. -/
theorem integral_log_affine_upper {a b al m r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 < al - m) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ Set.Icc a b, |(t - m) / (al - m)| ≤ r) (n : ℕ) :
    (∫ t in a..b, log (al - t) / (2 * t)) ≤
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * log (b / a)) -
        (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
          (∫ t in a..b, (t - m) ^ (i + 1) / t) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hmem' : ∀ t ∈ Set.Icc a b, (0 : ℝ) < t := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  have hxr' : ∀ t ∈ uIcc a b, |(t - m) / (al - m)| ≤ r := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hxr t ht
  have hpos : ∀ t ∈ Set.Icc a b, (0 : ℝ) < al - t := by
    intro t ht
    have h3 : (t - m) / (al - m) < 1 := (abs_lt.mp (lt_of_le_of_lt (hxr t ht) hr1)).2
    have h6 : t - m < al - m := (div_lt_one hD).mp h3
    linarith
  -- pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b,
      log (al - t) / (2 * t) ≤
        (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
          r ^ (n + 1) / (1 - r)) / (2 * t) := by
    intro t ht
    have h2t : (0 : ℝ) < 2 * t := by linarith [hmem' t ht]
    exact div_le_div_of_nonneg_right (log_affine_le_series hD hr0 hr1 (hxr t ht) n) h2t.le
  have hcont1 : ContinuousOn (fun t : ℝ => log (al - t) / (2 * t)) (uIcc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine ContinuousOn.log (continuousOn_const.sub continuousOn_id) ?_
      intro t ht
      have h3 : (t - m) / (al - m) < 1 := (abs_lt.mp (lt_of_le_of_lt (hxr' t ht) hr1)).2
      have h6 : t - m < al - m := (div_lt_one hD).mp h3
      intro hcon
      linarith [hcon]
    · intro t ht
      have h2t : (0 : ℝ) < 2 * t := by linarith [hmem t ht]
      positivity
  have hcont2 : ContinuousOn (fun t : ℝ =>
      (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
        r ^ (n + 1) / (1 - r)) / (2 * t)) (uIcc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine ContinuousOn.add (ContinuousOn.sub continuousOn_const ?_) continuousOn_const
      refine continuousOn_finsetSum (Finset.range n) (fun i _ => ?_)
      exact (((continuousOn_id.sub continuousOn_const).div_const _).pow _).div_const _
    · intro t ht
      have h2t : (0 : ℝ) < 2 * t := by linarith [hmem t ht]
      positivity
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1.intervalIntegrable hcont2.intervalIntegrable hpt
  -- integrability of the pieces of the right-hand side
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))
  have hterm : ∀ i ∈ Finset.range n, IntervalIntegrable
      (fun t : ℝ => (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        ((t - m) ^ (i + 1) / t)) volume a b := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    exact ((continuousOn_id.sub continuousOn_const).pow _).div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht))
  -- split the series against `1/t`
  have hsum_eq : ∀ t ∈ uIcc a b,
      (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) / t =
      ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        ((t - m) ^ (i + 1) / t) := by
    intro t _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow]
    field_simp
  have hcongr : ∀ t ∈ uIcc a b,
      (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
          r ^ (n + 1) / (1 - r)) / (2 * t) =
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t)) -
        (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
          ((t - m) ^ (i + 1) / t) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    rw [← hsum_eq t ht]
    field_simp
    ring
  have hA : IntervalIntegrable
      (fun t : ℝ => (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t))) volume a b :=
    (hinv.const_mul (log (al - m) + r ^ (n + 1) / (1 - r))).const_mul (1 / 2)
  have hS : IntervalIntegrable (fun t : ℝ => (1 / 2) * ∑ i ∈ Finset.range n,
      (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) * ((t - m) ^ (i + 1) / t))
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.const_mul ?_ _
    refine continuousOn_finsetSum (Finset.range n) (fun i _ => ?_)
    exact continuousOn_const.mul
      (((continuousOn_id.sub continuousOn_const).pow _).div continuousOn_id
        (fun t ht => ne_of_gt (hmem t ht)))
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hA hS] at hmono
  have e1 : (∫ t in a..b, (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t))) =
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * log (b / a)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_div_exp ha hab]
  have e2 : (∫ t in a..b, (1 / 2) * ∑ i ∈ Finset.range n,
        (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) * ((t - m) ^ (i + 1) / t)) =
      (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        (∫ t in a..b, (t - m) ^ (i + 1) / t) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hterm]
    refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
    rw [intervalIntegral.integral_const_mul]
  rw [e1, e2] at hmono
  linarith [hmono]

/-- `log (3969/3199)` two-sided, `x = 55/512`, ten terms. -/
theorem w3_log_ba : (0.215675912833547 : ℝ) ≤ log (3969/3199 : ℝ) ∧
    log (3969/3199 : ℝ) ≤ (0.215675912833548 : ℝ) := by
  have h := log_enclosure (y := (3969/3199 : ℝ)) (x := (55/512 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (1571/675)` from below, `x = 448/1123`, eighteen terms. -/
theorem w3_log_c1 : (0.844754947383091 : ℝ) ≤ log (1571/675 : ℝ) := by
  have h := log_enclosure (y := (1571/675 : ℝ)) (x := (448/1123 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 18
  refine le_trans ?_ h.1
  norm_num [Finset.sum_range_succ]

/-- `log (17/10)` from above, `x = 7/27`, fourteen terms. -/
theorem w3_log_17 : log (17/10 : ℝ) ≤ (0.530628251062171 : ℝ) := by
  have h := log_enclosure (y := (17/10 : ℝ)) (x := (7/27 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 14
  refine le_trans h.2 ?_
  norm_num [Finset.sum_range_succ]

/-- `log (617/540)` two-sided, `x = 77/1157`, eight terms. -/
theorem w3_log_617 : (0.133299884347067 : ℝ) ≤ log (617/540 : ℝ) ∧
    log (617/540 : ℝ) ≤ (0.133299884347068 : ℝ) := by
  have h := log_enclosure (y := (617/540 : ℝ)) (x := (77/1157 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 8
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `∫_{3199/2700}^{147/100} log (t+1)/t` from below: the `log (t+1)` series at the midpoint
`896/675` with 10 terms, ratio `385/6284`. -/
theorem w3_L_lower :
    (0.1815828256800 : ℝ) ≤ ∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (3199/2700 : ℝ) (147/100),
      |(896/675 - t) / (896/675 + 1)| ≤ 385/6284 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(896/675 : ℝ) - t| ≤ 77/540 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (896/675 : ℝ) + 1 = 1571/675 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 896/675 + 1), hden]
    have h3 : |(896/675 : ℝ) - t| / (1571/675) ≤ (77/540) / (1571/675) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (77/540 : ℝ) / (1571/675) = 385/6284 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (3199/2700 : ℝ)) (b := (147/100 : ℝ))
    (c := (896/675 : ℝ)) (r := (385/6284 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc1 := w3_log_c1
  have hba := w3_log_ba
  have hprod : (0.844754947383091 : ℝ) * (0.215675912833547 : ℝ) ≤
      log (1571/675 : ℝ) * log (3969/3199 : ℝ) :=
    mul_le_mul hc1 hba.1 (by norm_num) (le_trans (by norm_num) hc1)
  linarith [h, hprod, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `∫_{3199/2700}^{147/100} log (247/100 - t)/(2t) ≤ 0.014577579156`, 12 series terms around
`m = 896/675`, ratio `77/617`. -/
theorem w3_U_upper :
    (∫ t in (3199/2700 : ℝ)..(147/100 : ℝ), log ((247/100 : ℝ) - t) / (2 * t)) ≤
      (0.0145775791560 : ℝ) := by
  have hxr : ∀ t ∈ Set.Icc (3199/2700 : ℝ) (147/100),
      |(t - 896/675) / ((247/100 : ℝ) - 896/675)| ≤ 77/617 := by
    intro t ht
    have h1 : |t - (896/675 : ℝ)| ≤ 77/540 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 247/100 - 896/675)]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 247/100 - 896/675) (by norm_num : (0 : ℝ) < 617)]
    nlinarith [h1]
  have h := integral_log_affine_upper (a := (3199/2700 : ℝ)) (b := (147/100 : ℝ))
    (al := (247/100 : ℝ)) (m := (896/675 : ℝ)) (r := (77/617 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [integral_pow_sub_div (a := (3199/2700 : ℝ)) (b := (147/100 : ℝ)) (by norm_num) (by norm_num)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  have h1 := w3_log_617
  have h2 := w3_log_ba
  have hprod : log (617/540) * log (3969/3199) ≤
      (0.133299884347068 : ℝ) * (0.215675912833548 : ℝ) :=
    mul_le_mul h1.2 h2.2 (le_trans (by norm_num) h2.1) (by norm_num)
  nlinarith [h, h1.2, h2.1, h2.2, hprod]

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit2
