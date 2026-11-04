import LeanLab.RieselVaughan1983.Lemma15
import LeanLab.Common.ThetaWindowDusart
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Chebyshev MeasureTheory Set

namespace LeanLab.RieselVaughan1983

/-- LEAF. Page 56, (4.3): |θ(x) - x| < 0.000154 x / log x for log x ≥ 3000. Statement repaired
2026-10-31 by the architect, run 20261031T2235Z-16111: `hx0 : 0 < x` added; without it the leaf
was false at x = -exp 3000, see `LeanLab.Common.FalseLeafAudit20261031`. -/
theorem theta_bound_4_3 (x : ℝ) (hx0 : 0 < x) (hx : 3000 ≤ Real.log x) :
    |θ x - x| < 154 / 1000000 * x / Real.log x := by
  sorry

/-- LEAF. Page 56, (4.4): |θ(x) - x| < 0.00822 x / log x for 22 ≤ log x ≤ 5000. Statement
repaired 2026-10-31 by the architect, run 20261031T2235Z-16111: `hx0 : 0 < x` added; without it
the leaf was false at x = -exp 22. -/
theorem theta_bound_4_4 (x : ℝ) (hx0 : 0 < x) (hx1 : 22 ≤ Real.log x) (hx2 : Real.log x ≤ 5000) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  sorry

/-- LEAF. Page 57, combined bound: |θ(x) - x| < 0.00822 x / log x for log x ≥ 22. -/
theorem theta_bound_combined (x : ℝ) (hx0: 0 < x) (hx : 22 ≤ Real.log x) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  by_cases hx3000 : 3000 ≤ Real.log x
  · have h1 := theta_bound_4_3 x hx0 hx3000
    have h2 : (154 : ℝ) / 1000000 ≤ (822 : ℝ) / 100000 := by norm_num
    have h22 : (0 : ℝ) ≤ 22 := by norm_num
    have h3 : 0 ≤ x / Real.log x := div_nonneg hx0.le (h22.trans hx)
    calc |θ x - x| < 154 / 1000000 * x / Real.log x := h1
      _ = 154 / 1000000 * (x / Real.log x) := by ring
      _ ≤ 822 / 100000 * (x / Real.log x) := mul_le_mul_of_nonneg_right h2 h3
      _ = 822 / 100000 * x / Real.log x := by ring
  · push Not at hx3000
    have hx3000_le : Real.log x ≤ 5000 := hx3000.le.trans (by norm_num)
    exact theta_bound_4_4 x hx0 hx hx3000_le

/-! ## The page-57 argument for (4.2)

`lemma6ii_integral` below is re-cut with the page-56 theta bound (4.4) as a hypothesis, and its
proof is the paper's page-57 partial-summation argument, carried out from that hypothesis alone:
partial summation (4.6), the split at `y = e^22`, `π(y) ≤ y + 1`, the interval estimates
`A₂ ≤ 1.006818 x/log²x` and `A₃ ≤ 0.003385 x/log²x` of page 57, and the arithmetic of the
constants, which leaves about `1.4·10⁻⁵` of slack in the target constant `1.0151`.
Auxiliary lemmas, all private. -/

private lemma exp22_gt_one : (1 : ℝ) < Real.exp 22 := by
  have h := Real.add_one_le_exp (22 : ℝ); linarith

private lemma two_le_exp22 : (2 : ℝ) ≤ Real.exp 22 := by
  have h := Real.add_one_le_exp (22 : ℝ); linarith

private lemma log_ge_22 {t : ℝ} (ht : Real.exp 22 ≤ t) : 22 ≤ Real.log t := by
  rw [← Real.log_exp (22 : ℝ)]
  exact Real.log_le_log (Real.exp_pos 22) ht

/-- `1/2 <= log 2`. -/
private lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp (1 / 2) ^ 2 < 4 := by
    rw [h1]; linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

/-- `log 4 <= 2`. -/
private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.add_one_le_exp 1]
  linarith

private lemma hd2 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 2)
    (1 / (Real.log t) ^ 2 - 2 / (Real.log t) ^ 3) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 2) (2 * (Real.log t) ^ 1 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 2
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 2 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

private lemma hd3 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 3)
    (1 / (Real.log t) ^ 3 - 3 / (Real.log t) ^ 4) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 3) (3 * (Real.log t) ^ 2 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 3
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 3 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

private lemma hd4 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 4)
    (1 / (Real.log t) ^ 4 - 4 / (Real.log t) ^ 5) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 4) (4 * (Real.log t) ^ 3 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 4
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 4 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

private lemma hd5 {t : ℝ} (ht : 1 < t) : HasDerivAt (fun s : ℝ => s / (Real.log s) ^ 5)
    (1 / (Real.log t) ^ 5 - 5 / (Real.log t) ^ 6) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : HasDerivAt (Real.log ^ 5) (5 * (Real.log t) ^ 4 * (1 / t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht0).pow 5
  have hnum : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h := hnum.div hden (pow_ne_zero 5 hlog)
  convert h using 1
  field_simp
  simp only [Pi.pow_def]
  ring

/-! ## 4. Integrability of `1 / log^k t` -/

private lemma ii_inv_log_pow (k : ℕ) {Y x : ℝ} (hY : 1 < Y) (hYx : Y ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ k) volume Y x := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hYx] at ht
  have htY : 1 < t := lt_of_lt_of_le hY ht.1
  have hne : Real.log t ≠ 0 := (Real.log_pos htY).ne'
  have hcont : ContinuousAt (fun s : ℝ => (Real.log s) ^ k) t :=
    (Real.continuousAt_log (by linarith : t ≠ 0)).pow k
  have hinv : ContinuousAt (fun s : ℝ => ((Real.log s) ^ k)⁻¹) t :=
    ContinuousAt.inv₀ hcont (pow_ne_zero k hne)
  simpa [one_div] using hinv.continuousWithinAt

/-! ## 5. The fundamental-theorem recurrence `A_k = x/log^k x - Y/log^k Y + k A_{k+1}` -/

private lemma ftoc_expand (k : ℕ) {Y x : ℝ} (hY : 1 < Y) (hYx : Y ≤ x)
    (hd : ∀ t ∈ uIcc Y x, HasDerivAt (fun s : ℝ => s / (Real.log s) ^ k)
      (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) t) :
    ∫ t in Y..x, 1 / (Real.log t) ^ k
      = x / (Real.log x) ^ k - Y / (Real.log Y) ^ k
        + (k : ℝ) * ∫ t in Y..x, 1 / (Real.log t) ^ (k + 1) := by
  have hik := ii_inv_log_pow k hY hYx
  have hik1 := ii_inv_log_pow (k + 1) hY hYx
  have hcont : IntervalIntegrable
      (fun t : ℝ => 1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      volume Y x := hik.sub (hik1.const_mul (k : ℝ))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont
  rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul] at h
  linarith

/-! ## 6. The decaying bound `A_k <= x/(log^k x * (1 - k/22))` -/

private lemma A_decay (k : ℕ) (hk22 : (k : ℝ) < 22) {Y x : ℝ}
    (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hd : ∀ t ∈ uIcc Y x, HasDerivAt (fun s : ℝ => s / (Real.log s) ^ k)
      (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) t) :
    ∫ t in Y..x, 1 / (Real.log t) ^ k ≤ x / (Real.log x) ^ k / (1 - (k : ℝ) / 22) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have hik := ii_inv_log_pow k hY hYx
  have hik1 := ii_inv_log_pow (k + 1) hY hYx
  have hcont : IntervalIntegrable
      (fun t : ℝ => 1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      volume Y x := hik.sub (hik1.const_mul (k : ℝ))
  have hftoc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont
  rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul] at hftoc
  -- pointwise comparison against `(1 - k/22) * 1/log^k t`
  have hcmp : ∫ t in Y..x, (1 - (k : ℝ) / 22) * (1 / (Real.log t) ^ k)
      ≤ ∫ t in Y..x,
          (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1))) := by
    refine intervalIntegral.integral_mono_on hYx (hik.const_mul _) hcont ?_
    intro t ht
    have htY : Real.exp 22 ≤ t := le_trans hYexp ht.1
    have hL22 : 22 ≤ Real.log t := log_ge_22 htY
    have hL : 0 < Real.log t := by linarith
    have hp : (0 : ℝ) ≤ 1 / (Real.log t) ^ k := by positivity
    have hkL : (k : ℝ) / Real.log t ≤ (k : ℝ) / 22 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL22
    have key : (1 - (k : ℝ) / 22) ≤ 1 - (k : ℝ) / Real.log t := by linarith
    refine (mul_le_mul_of_nonneg_right key hp).trans_eq ?_
    rw [pow_succ]
    field_simp
  have hpos : 0 < 1 - (k : ℝ) / 22 := by
    have hle : (k : ℝ) / 22 < 1 := by
      rw [div_lt_one (by norm_num)]; exact hk22
    linarith
  have hsplit : ∫ t in Y..x,
        (1 / (Real.log t) ^ k - (k : ℝ) * (1 / (Real.log t) ^ (k + 1)))
      = (∫ t in Y..x, 1 / (Real.log t) ^ k)
        - (k : ℝ) * ∫ t in Y..x, 1 / (Real.log t) ^ (k + 1) := by
    rw [intervalIntegral.integral_sub hik (hik1.const_mul (k : ℝ)),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hftoc, intervalIntegral.integral_const_mul] at hcmp
  have hdrop : x / (Real.log x) ^ k - Y / (Real.log Y) ^ k ≤ x / (Real.log x) ^ k := by
    have : 0 ≤ Y / (Real.log Y) ^ k := by
      have hYpos : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
      positivity
    linarith
  rw [le_div_iff₀ hpos]
  linarith


/-! ## 7. The three expansions used on page 57 -/

private lemma A2_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 + 2 * ∫ t in Y..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 2 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd2 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 2 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

private lemma A3_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 3 + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 3 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd3 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 3 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

private lemma A4_expand {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 4
      ≤ x / (Real.log x) ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5 := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := ftoc_expand 4 hY hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd4 ht1
    convert hd using 1
    ring)
  have hpos : 0 ≤ Y / (Real.log Y) ^ 4 := by
    have hL : 0 < Real.log Y := by have := log_ge_22 hYexp; linarith
    positivity
  linarith

/-- `A_2 <= x/log^2 x * (1 + 2/log x + 6/log^2 x + 528/(17 log^3 x))`. -/
private lemma A2_bound {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have e2 := A2_expand hYexp hYx
  have e3 := A3_expand hYexp hYx
  have e4 := A4_expand hYexp hYx
  have e5 : ∫ t in Y..x, 1 / (Real.log t) ^ 5 ≤ 22 * x / (17 * (Real.log x) ^ 5) := by
    have h := A_decay 5 (by norm_num) hYexp hYx (fun t ht => by
      rw [uIcc_of_le hYx] at ht
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
      have hd := hd5 ht1
      convert hd using 1
      ring)
    refine h.trans_eq ?_
    field_simp
    ring
  have step1 : ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4) := by linarith [e2, e3]
  have step2 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
        + 3 * ∫ t in Y..x, 1 / (Real.log t) ^ 4)
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5)) := by
    linarith [e4]
  have step3 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
        + 3 * (x / Real.log x ^ 4 + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5))
      ≤ x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * (22 * x / (17 * Real.log x ^ 5)))) := by
    linarith [e5]
  have s1 : ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
        + 24 * (22 * x / (17 * Real.log x ^ 5)) := by
    have h4 : x / Real.log x ^ 2 + 2 * (x / Real.log x ^ 3
          + 3 * (x / Real.log x ^ 4 + 4 * (22 * x / (17 * Real.log x ^ 5))))
        = x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
          + 24 * (22 * x / (17 * Real.log x ^ 5)) := by ring
    linarith [step1, step2, step3, h4]
  have hrw : x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4
      + 24 * (22 * x / (17 * Real.log x ^ 5))
      = x / Real.log x ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := by
    have hL : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by
        have h22 : Real.exp 22 ≤ x := le_trans hYexp hYx
        have := log_ge_22 h22; linarith
      linarith
    field_simp
    ring
  rw [hrw] at s1
  exact s1

/-- The piece on `[2, exp 22]` costs at most `8 exp 22`, by Chebyshev's `theta t <= log 4 * t`
and `log t >= log 2 >= 1/2` there. -/
private lemma head_le :
    ∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2) ≤ 8 * Real.exp 22 := by
  have h2Y : (2 : ℝ) ≤ Real.exp 22 := two_le_exp22
  have hintθ : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le h2Y]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hmono : ∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2)
      ≤ ∫ t in (2 : ℝ)..Real.exp 22, (8 : ℝ) := by
    refine intervalIntegral.integral_mono_on h2Y hintθ (by simp) ?_
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    have hL2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hLhalf : (1 / 2 : ℝ) ≤ Real.log t := le_trans log_two_ge_half hL2
    have hsq : (1 / 4 : ℝ) ≤ (Real.log t) ^ 2 := by nlinarith
    have hθt : θ t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
    nlinarith [hθt, hsq, ht0, log_four_le_two]
  have hconst : ∫ t in (2 : ℝ)..Real.exp 22, (8 : ℝ) = 8 * (Real.exp 22 - 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hconst] at hmono
  nlinarith [hmono, h2Y, Real.exp_pos 22]

/-- The piece on `[exp 22, x]`, using `theta t <= t + 0.00822 t/log t`. -/
private lemma tail_le {x : ℝ} (hYexp : Real.exp 22 ≤ x)
    (hint : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + 822 / 100000 * t / Real.log t) :
    ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ (∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 2)
        + 822 / 100000 * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Real.exp 22 := exp22_gt_one
  have hpt : (∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2))
      ≤ ∫ t in Real.exp 22..x,
          (1 / (Real.log t) ^ 2 + 822 / 100000 * (1 / (Real.log t) ^ 3)) := by
    refine intervalIntegral.integral_mono_on hYexp hint ?_ ?_
    · -- integrability of the comparison function
      have h2 := ii_inv_log_pow 2 hY hYexp
      have h3 := ii_inv_log_pow 3 hY hYexp
      exact h2.add (h3.const_mul _)
    · intro t ht
      have htY : Real.exp 22 ≤ t := ht.1
      have hL22 : 22 ≤ Real.log t := log_ge_22 htY
      have hL : 0 < Real.log t := by linarith
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) htY
      have h1 := hθ t htY
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have hkey : (1 / Real.log t ^ 2 + 822 / 100000 * (1 / Real.log t ^ 3))
          * (t * Real.log t ^ 2) = t + 822 / 100000 * t / Real.log t := by
        field_simp
      rw [hkey]
      exact h1
  refine hpt.trans_eq ?_
  rw [intervalIntegral.integral_add (ii_inv_log_pow 2 hY hYexp)
    ((ii_inv_log_pow 3 hY hYexp).const_mul _), intervalIntegral.integral_const_mul]

/-! ## 9. The quantitative leftovers -/

/-- `(1 + s/300)^2 <= exp s` for `s >= 0`. -/
private lemma one_add_sq_le_exp {s : ℝ} (hs : 0 ≤ s) : (1 + s / 300) ^ 2 ≤ Real.exp s := by
  have hsum : ∑ i ∈ Finset.range 3, s ^ i / (Nat.factorial i : ℝ) ≤ Real.exp s :=
    Real.sum_le_exp_of_nonneg hs 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
  norm_num at hsum
  nlinarith [hs, sq_nonneg s]

/-- `exp 300 / 300^2 <= x / (log x)^2` for `log x >= 300`. -/
private lemma exp300_div_sq_le {x L : ℝ} (hx0 : 0 < x) (hLx : L = Real.log x) (hL : 300 ≤ L) :
    Real.exp 300 / 300 ^ 2 ≤ x / L ^ 2 := by
  have hxexp : x = Real.exp L := by rw [hLx]; exact (Real.exp_log hx0).symm
  set s := L - 300 with hs
  have hs0 : 0 ≤ s := by linarith
  have hLs : L = 300 + s := by linarith
  rw [hxexp, hLs, Real.exp_add]
  have hkey := one_add_sq_le_exp hs0
  have hmain : (300 + s) ^ 2 ≤ 300 ^ 2 * Real.exp s := by
    have hsq : (300 + s) ^ 2 = 300 ^ 2 * (1 + s / 300) ^ 2 := by
      field_simp
    rw [hsq]
    nlinarith [hkey, sq_nonneg (1 + s / 300)]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 300 ^ 2), div_mul_eq_mul_div,
    le_div_iff₀ (by nlinarith : (0 : ℝ) < (300 + s) ^ 2)]
  nlinarith [hmain, Real.exp_pos 300]

private lemma exp278_gt_big : (72000000000 : ℝ) < Real.exp 278 := by
  have h : Real.exp 278 = Real.exp 1 ^ 278 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h40 : (72000000000 : ℝ) < (2 : ℝ) ^ 40 := by norm_num
  have h3 : (2 : ℝ) ^ 40 < (2 : ℝ) ^ 278 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h4 : (2 : ℝ) ^ 278 ≤ Real.exp 1 ^ 278 := pow_le_pow_left₀ (by norm_num) h2 278
  calc (72000000000 : ℝ) < (2 : ℝ) ^ 40 := h40
    _ < (2 : ℝ) ^ 278 := h3
    _ ≤ Real.exp 1 ^ 278 := h4
    _ = Real.exp 278 := h.symm

/-- `A_5 <= 22 x/(17 log^5 x)`, the decaying end of the recurrence. -/
private lemma A5_le {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 5 ≤ 22 * x / (17 * (Real.log x) ^ 5) := by
  have hY : 1 < Y := lt_of_lt_of_le exp22_gt_one hYexp
  have h := A_decay 5 (by norm_num) hYexp hYx (fun t ht => by
    rw [uIcc_of_le hYx] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY ht.1
    have hd := hd5 ht1
    convert hd using 1
    ring)
  refine h.trans_eq ?_
  field_simp
  ring

/-- `A_3 <= x/log^2 x * (1/log x + 3/log^2 x + 264/(17 log^3 x))`, the sharper form needed to
reach the paper's `0.003385`. -/
private lemma A3_sharp {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := by
  have e3 := A3_expand hYexp hYx
  have e4 := A4_expand hYexp hYx
  have e5 := A5_le hYexp hYx
  have s1 : ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
          + 4 * ∫ t in Y..x, 1 / (Real.log t) ^ 5) := by linarith [e3, e4]
  have s2 : ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
          + 4 * (22 * x / (17 * Real.log x ^ 5))) := by linarith [s1, e5]
  have hrw : x / Real.log x ^ 3 + 3 * (x / Real.log x ^ 4
        + 4 * (22 * x / (17 * Real.log x ^ 5)))
      = x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := by
    have hL : Real.log x ≠ 0 := by
      have : 0 < Real.log x := by
        have h22 : Real.exp 22 ≤ x := le_trans hYexp hYx
        have := log_ge_22 h22; linarith
      linarith
    field_simp
    ring
  rw [hrw] at s2
  exact s2

/-- Page 57: `A_2 <= 1.006818 x/log^2 x` for `log x >= 300`. -/
private lemma A2_le_paper {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hL : 300 ≤ Real.log x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 2 ≤ 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by
  have h := A2_bound hYexp hYx
  have hkey : 1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)
      ≤ 1006818 / 1000000 := by
    have h1 : 2 / Real.log x ≤ 2 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2 : 6 / (Real.log x) ^ 2 ≤ 6 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : 528 / (17 * (Real.log x) ^ 3) ≤ 528 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith [h1, h2, h3]
  have hB : 0 ≤ x / (Real.log x) ^ 2 := by
    have hpos : 0 < Real.log x := by linarith
    exact div_nonneg (by linarith [Real.exp_pos 22, hYexp, hYx]) (by positivity)
  calc ∫ t in Y..x, 1 / (Real.log t) ^ 2
      ≤ x / (Real.log x) ^ 2 *
          (1 + 2 / Real.log x + 6 / (Real.log x) ^ 2 + 528 / (17 * (Real.log x) ^ 3)) := h
    _ ≤ x / (Real.log x) ^ 2 * (1006818 / 1000000) := mul_le_mul_of_nonneg_left hkey hB
    _ = 1006818 / 1000000 * (x / (Real.log x) ^ 2) := by ring

/-- Page 57: `A_3 <= 0.003385 x/log^2 x` for `log x >= 300`. -/
private lemma A3_le_paper {Y x : ℝ} (hYexp : Real.exp 22 ≤ Y) (hYx : Y ≤ x)
    (hL : 300 ≤ Real.log x) :
    ∫ t in Y..x, 1 / (Real.log t) ^ 3 ≤ 3385 / 1000000 * (x / (Real.log x) ^ 2) := by
  have h := A3_sharp hYexp hYx
  have hkey : 1 / Real.log x + 3 / (Real.log x) ^ 2 + 264 / (17 * (Real.log x) ^ 3)
      ≤ 3385 / 1000000 := by
    have h1 : 1 / Real.log x ≤ 1 / 300 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h2 : 3 / (Real.log x) ^ 2 ≤ 3 / 300 ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h3 : 264 / (17 * (Real.log x) ^ 3) ≤ 264 / (17 * 300 ^ 3) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith [h1, h2, h3]
  have hB : 0 ≤ x / (Real.log x) ^ 2 := by
    have hpos : 0 < Real.log x := by linarith
    exact div_nonneg (by linarith [Real.exp_pos 22, hYexp, hYx]) (by positivity)
  calc ∫ t in Y..x, 1 / (Real.log t) ^ 3
      ≤ x / (Real.log x) ^ 2 * (1 / Real.log x + 3 / (Real.log x) ^ 2
          + 264 / (17 * (Real.log x) ^ 3)) := h
    _ ≤ x / (Real.log x) ^ 2 * (3385 / 1000000) := mul_le_mul_of_nonneg_left hkey hB
    _ = 3385 / 1000000 * (x / (Real.log x) ^ 2) := by ring

/-- The endpoint term at the sharper allowance `10^-5`. -/
private lemma eight_exp22_lt_1e5 {x L : ℝ} (hx0 : 0 < x) (hLx : L = Real.log x) (hL : 300 ≤ L) :
    8 * Real.exp 22 < 1 / 100000 * (x / L ^ 2) := by
  have h1 := exp300_div_sq_le hx0 hLx hL
  have h300 : Real.exp 300 = Real.exp 22 * Real.exp 278 := by
    rw [← Real.exp_add]; norm_num
  have hbig : 8 * Real.exp 22 < 1 / 100000 * (Real.exp 300 / 300 ^ 2) := by
    rw [h300]
    have hp : (0 : ℝ) < Real.exp 22 := Real.exp_pos 22
    have h278 := exp278_gt_big
    rw [show (1 : ℝ) / 100000 * (Real.exp 22 * Real.exp 278 / 300 ^ 2)
        = Real.exp 22 * (Real.exp 278 / (100000 * 300 ^ 2)) by ring]
    have hle : (8 : ℝ) < Real.exp 278 / (100000 * 300 ^ 2) := by
      rw [lt_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  calc 8 * Real.exp 22 < 1 / 100000 * (Real.exp 300 / 300 ^ 2) := hbig
    _ ≤ 1 / 100000 * (x / L ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- The whole page-57 budget, as a single constant inequality: with the paper's `1.006818` and
`0.003385` and an endpoint allowance of `10^-5`, an input constant `c` leaves the paper's
`1.0151` intact as long as `c` is at most `0.00823`. -/
private lemma const_sum_param {c : ℝ} (_hc0 : 822 / 100000 ≤ c) (hc : c ≤ 823 / 100000) :
    c + 1 / 100000 + 1006818 / 1000000 + c * (3385 / 1000000) < 10151 / 10000 := by
  nlinarith

/-- `tail_le` with the error constant left symbolic. -/
private lemma tail_le_const {x c : ℝ} (hYexp : Real.exp 22 ≤ x)
    (hint : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t) :
    ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ (∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 2)
        + c * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3 := by
  have hY : 1 < Real.exp 22 := exp22_gt_one
  have hpt : (∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2))
      ≤ ∫ t in Real.exp 22..x,
          (1 / (Real.log t) ^ 2 + c * (1 / (Real.log t) ^ 3)) := by
    refine intervalIntegral.integral_mono_on hYexp hint ?_ ?_
    · have h2 := ii_inv_log_pow 2 hY hYexp
      have h3 := ii_inv_log_pow 3 hY hYexp
      exact h2.add (h3.const_mul _)
    · intro t ht
      have htY : Real.exp 22 ≤ t := ht.1
      have hL22 : 22 ≤ Real.log t := log_ge_22 htY
      have hL : 0 < Real.log t := by linarith
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) htY
      have h1 := hθ t htY
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have hkey : (1 / Real.log t ^ 2 + c * (1 / Real.log t ^ 3))
          * (t * Real.log t ^ 2) = t + c * t / Real.log t := by
        field_simp
      rw [hkey]
      exact h1
  refine hpt.trans_eq ?_
  rw [intervalIntegral.integral_add (ii_inv_log_pow 2 hY hYexp)
    ((ii_inv_log_pow 3 hY hYexp).const_mul _), intervalIntegral.integral_const_mul]

/-- Lemma 6 (ii) from the pointwise input with the paper's own page-57 constants, and with the
input constant allowed to be anything in `[0.00822, 0.00823]`: the accumulated slack is then
`10151/10000 - 0.00823 - 10^-5 - 1.006818 - 0.00823 * 0.003385 = 1.4 * 10^-5`, so the target
constant `1.0151` is essentially tight against the input. -/
private theorem lemma6ii_of_theta_upper_const (c : ℝ) (hc0 : 822 / 100000 ≤ c)
    (hc : c ≤ 823 / 100000)
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + c * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  have hlogpos : 0 < Real.log x := by linarith
  have hcpos : (0 : ℝ) ≤ c := by linarith
  have hYexp : Real.exp 22 ≤ x := by
    rw [← Real.exp_log hx0]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2x : (2 : ℝ) ≤ x := le_trans two_le_exp22 hYexp
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral h2x
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume 2 (Real.exp 22) := by
    rw [intervalIntegrable_iff, uIoc_of_le two_le_exp22]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq (Real.exp 22)).mono_set
      Set.Ioc_subset_Icc_self
  have hint2 : IntervalIntegrable (fun t : ℝ => θ t / (t * Real.log t ^ 2))
      volume (Real.exp 22) x := by
    rw [intervalIntegrable_iff, uIoc_of_le hYexp]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun t ht => ⟨le_trans two_le_exp22 ht.1.le, ht.2⟩)
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
        + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hhead := head_le
  have htail0 := tail_le_const hYexp hint2 hθ
  have hA2 := A2_le_paper (Y := Real.exp 22) le_rfl hYexp hL
  have hA3 := A3_le_paper (Y := Real.exp 22) le_rfl hYexp hL
  have hsmall := eight_exp22_lt_1e5 hx0 rfl hL
  have hconst := const_sum_param hc0 hc
  -- theta at x
  have hthx : θ x / Real.log x ≤ x / Real.log x + c * (x / Real.log x ^ 2) := by
    have h1 : θ x ≤ x + c * x / Real.log x := hθ x hYexp
    have hid2 : x / Real.log x + c * (x / Real.log x ^ 2)
        = (x + c * x / Real.log x) / Real.log x := by
      field_simp
    rw [hid2]
    exact div_le_div_of_nonneg_right h1 hlogpos.le
  -- the `A_3` term, scaled by `c`
  have hA3c : c * ∫ t in Real.exp 22..x, 1 / (Real.log t) ^ 3
      ≤ c * (3385 / 1000000 * (x / Real.log x ^ 2)) :=
    mul_le_mul_of_nonneg_left hA3 hcpos
  have htail : ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ 1006818 / 1000000 * (x / Real.log x ^ 2)
        + c * (3385 / 1000000 * (x / Real.log x ^ 2)) := by
    have := htail0
    linarith [hA2, hA3c]
  -- the arithmetic
  have hBpos : 0 < x / Real.log x ^ 2 := div_pos hx0 (pow_pos hlogpos 2)
  have hkey : c * (x / Real.log x ^ 2) + 8 * Real.exp 22
      + 1006818 / 1000000 * (x / Real.log x ^ 2)
      + c * (3385 / 1000000 * (x / Real.log x ^ 2))
      < 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h2 := mul_lt_mul_of_pos_right hconst hBpos
    have hsum : (c + 1 / 100000 + 1006818 / 1000000 + c * (3385 / 1000000))
          * (x / Real.log x ^ 2)
        = c * (x / Real.log x ^ 2) + 1 / 100000 * (x / Real.log x ^ 2)
          + 1006818 / 1000000 * (x / Real.log x ^ 2)
          + c * (3385 / 1000000 * (x / Real.log x ^ 2)) := by
      field_simp
    rw [hsum] at h2
    nlinarith [h2, hsmall.le, hBpos]
  -- assemble
  rw [hid, hsplit]
  have e1 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22 := by
    linarith [hthx, hhead]
  have e2 : θ x / Real.log x + (∫ t in (2 : ℝ)..Real.exp 22, θ t / (t * Real.log t ^ 2))
      + ∫ t in Real.exp 22..x, θ t / (t * Real.log t ^ 2)
      ≤ x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + (1006818 / 1000000 * (x / Real.log x ^ 2)
            + c * (3385 / 1000000 * (x / Real.log x ^ 2))) := by
    linarith [e1, htail]
  have e3 : x / Real.log x + c * (x / Real.log x ^ 2) + 8 * Real.exp 22
        + (1006818 / 1000000 * (x / Real.log x ^ 2)
            + c * (3385 / 1000000 * (x / Real.log x ^ 2)))
      < x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by
    have h := add_lt_add_left hkey (x / Real.log x)
    linarith [h]
  have hgoal : x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2
      = x / Real.log x + 10151 / 10000 * (x / Real.log x ^ 2) := by ring
  rw [hgoal]
  linarith [e2, e3]

/-- The paper's own numbers: Lemma 6 (ii) from `theta t <= t + 0.00822 t/log t`. -/
private theorem lemma6ii_of_theta_upper_paper
    (hθ : ∀ t : ℝ, Real.exp 22 ≤ t → θ t ≤ t + 822 / 100000 * t / Real.log t)
    (x : ℝ) (hx0 : 0 < x) (hL : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 :=
  lemma6ii_of_theta_upper_const (822 / 100000) le_rfl (by norm_num) hθ x hx0 hL


/-! ## 14. The paper's combined integral estimate `I < 1.006818 x/log^2 x`

Page 57 does not estimate `A_2` and `A_3` separately: it bounds
`I = int_y^x (1 + delta/log u) du/log^2 u` in one go by `1.006818 x/log^2 x`, with
`delta = 0.00822` already inside the constant. Section 13 estimated `A_2 <= 1.006818 B` and then
charged `delta A_3` on top, which spends about `2.8 * 10^-5` of the budget twice. Doing it the
paper's way leaves `6.2 * 10^-5` of slack instead of `3.4 * 10^-5`, so the input constant may go
up to `0.00825` instead of `0.00823`. -/

/-- LEAF. Page 57, integral bound for prime counting: `π(x) < x/log x + 1.0151 x/(log x)²` for
`log x ≥ 300`, from the theta bound (4.4) on page 56. REPAIRED 2026-11-04, run
`lomos 20261104T1614Z`: the leaf was true but had no route inside the file or Mathlib (it is an
explicit form of the prime number theorem, and Mathlib has no explicit PNT), so it is re-cut with
the theta bound of the sibling leaves as a hypothesis,
`hθ : ∀ t, 0 < t → 22 ≤ log t → |θ t - t| < 0.00822 t/log t`, which the assembly
`lemma6ii_decomposed` supplies from `theta_bound_combined`. Since `|θ t - t| < c` gives the
one-sided `θ t ≤ t + c` used on page 56, nothing is lost in the paper's own argument. -/
theorem lemma6ii_integral (x : ℝ) (hx0 : 0 < x) (hx300 : 300 ≤ Real.log x)
    (hθ : ∀ t : ℝ, 0 < t → 22 ≤ Real.log t → |θ t - t| < 822 / 100000 * t / Real.log t) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  refine lemma6ii_of_theta_upper_paper ?_ x hx0 hx300
  intro t htY
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 22) htY
  have hL : 22 ≤ Real.log t := log_ge_22 htY
  have h := hθ t ht0 hL
  linarith [le_abs_self (θ t - t)]

/-- The exact cited statement of Lemma 6 (ii). -/
theorem lemma6ii_decomposed : Lemma6ii := by
  intro x hx0 hx300
  exact lemma6ii_integral x hx0 hx300 theta_bound_combined

end LeanLab.RieselVaughan1983
