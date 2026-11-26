import LeanLab.RieselVaughan1983.ParameterBounds709
import LeanLab.RieselVaughan1983.ParameterLog709
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Localization of the root chosen on Schoenfeld 1976 page 345.
The tail domain X at least 14 is sufficient for the assigned exponential leaf.
No effective zero-sum estimate is assumed or proved here.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Set

namespace LeanLab.RieselVaughan1983.Task709

/-- A lower bound for the logarithmic trial points in equation 7.29.
It covers both source coefficients 2 and 5 on the required tail. -/
theorem schoenfeld_log_trial_lower (X c : ℝ) (hX : 14 ≤ X) (hc : 2 ≤ c) :
    6 / 7 < 1 - log (17 * X / (c * Real.pi)) / (2 * X) := by
  have hX0 : 0 < X := by linarith
  have hc0 : 0 < c := by linarith
  have hq : 0 < (17 * 14 : ℝ) / (c * Real.pi) := by positivity
  have hq40 : (17 * 14 : ℝ) / (c * Real.pi) < 40 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < c * Real.pi)).mpr
    have hprod := mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have he4 : (40 : ℝ) < exp 4 := by
    calc
      _ < (2.7182818283 : ℝ) ^ 4 := by norm_num
      _ ≤ exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 4
      _ = exp 4 := by rw [← exp_nat_mul]; norm_num
  have hlog14 : log ((17 * 14 : ℝ) / (c * Real.pi)) < 4 :=
    (log_lt_iff_lt_exp hq).mpr (hq40.trans he4)
  have hsplit : log (17 * X / (c * Real.pi)) =
      log (X / 14) + log ((17 * 14 : ℝ) / (c * Real.pi)) := by
    rw [← log_mul (by positivity : X / 14 ≠ 0) hq.ne']
    congr 1
    field_simp [hc0.ne', Real.pi_ne_zero]
  have htangent := log_le_sub_one_of_pos (show 0 < X / 14 by positivity)
  have hlog : log (17 * X / (c * Real.pi)) < 2 / 7 * X := by
    rw [hsplit]
    linarith
  have hdiv : log (17 * X / (c * Real.pi)) / (2 * X) < 1 / 7 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * X)).mpr
    linarith
  linarith

/-- The lower root localization in equation 7.30 on page 345,
restricted to the tail X at least 14 used by the assigned source leaf. -/
theorem schoenfeld_root_gt_log_trial (X v : ℝ) (hX : 14 ≤ X)
    (hv : v ∈ Ioo (sqrt (1 / 2)) 1)
    (hroot : schoenfeldK X (log (17 / (2 * Real.pi))) v = 1) :
    1 - log (17 * X / (2 * Real.pi)) / (2 * X) < v := by
  let d : ℝ := log (17 / (2 * Real.pi))
  let q : ℝ := 17 * X / (2 * Real.pi)
  let w : ℝ := 1 - log q / (2 * X)
  have hX0 : 0 < X := by linarith
  have hbase : (0 : ℝ) < 17 / (2 * Real.pi) := by positivity
  have hd : (1 / 4 : ℝ) ≤ d := by
    have htwo : (2 : ℝ) ≤ 17 / (2 * Real.pi) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      nlinarith [Real.pi_lt_four]
    have h := log_le_log (by norm_num : (0 : ℝ) < 2) htwo
    dsimp [d]
    linarith [Real.log_two_gt_d9]
  have hd0 : 0 ≤ d := by linarith
  have hwlo : 6 / 7 < w := schoenfeld_log_trial_lower X 2 hX (by norm_num)
  have hw0 : 0 < w := by linarith
  have hq1 : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hq0 : 0 < q := by linarith
  have hw1 : w < 1 := by
    have hp := div_pos (log_pos hq1) (show 0 < 2 * X by positivity)
    dsimp [w]
    linarith
  have hwden : 1 < 2 * w ^ 2 := by nlinarith [sq_nonneg (w - 6 / 7)]
  have hbasex : (17 : ℝ) / (2 * Real.pi) < X := by
    have hthree : (17 : ℝ) / (2 * Real.pi) < 3 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      nlinarith [Real.pi_gt_three]
    linarith
  have hdlog : d < log X := log_lt_log hbase hbasex
  have hlogs : log q = d + log X := by
    dsimp [q, d]
    rw [← log_mul hbase.ne' hX0.ne']
    congr 1
    ring
  have hsum : w + d / X < 1 := by
    have hneg : (d - log X) / (2 * X) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    have heq : w + d / X = 1 + (d - log X) / (2 * X) := by
      dsimp [w]
      rw [hlogs]
      field_simp [hX0.ne']
      ring
    rw [heq]
    linarith
  have hH := schoenfeldH_bounds X d w hX0 hd hw0 hwden hw1.le
  have hHlt : schoenfeldH X d w < 1 := by
    have hs0 : 0 < w + d / X := by positivity
    have hs : (w + d / X) ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hsum) (show 0 < 1 + (w + d / X) by positivity)]
    exact hH.2.trans hs
  have hH0 : 0 ≤ schoenfeldH X d w := by
    have hdiff : 0 < 2 * w ^ 2 - 1 := by linarith
    exact (show 0 ≤ w ^ 6 * (2 * w ^ 2 - 1) by positivity).trans hH.1.le
  have hsqrt : sqrt (schoenfeldH X d w) < 1 := by
    simpa using Real.sqrt_lt_sqrt hH0 hHlt
  have heval : schoenfeldK X d w = sqrt (schoenfeldH X d w) *
      exp (-(log q) ^ 2 / (4 * w * X)) := by
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
      schoenfeldK_at_log_parameter X 2 d hX0 (by norm_num) hw0
  have hexp : exp (-(log q) ^ 2 / (4 * w * X)) ≤ 1 := by
    apply exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (log q)])
      (by positivity)
  have hKw : schoenfeldK X d w < 1 := by
    rw [heval]
    calc
      _ ≤ sqrt (schoenfeldH X d w) * 1 :=
        mul_le_mul_of_nonneg_left hexp (sqrt_nonneg _)
      _ < 1 := by simpa using hsqrt
  have hv0 : 0 < v := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans hv.1
  have hvden : 1 < 2 * v ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hv.1)
      (show 0 < v + sqrt (1 / 2) by positivity)
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  change schoenfeldK X d v = 1 at hroot
  change w < v
  by_contra hnot
  rcases lt_or_eq_of_le (not_lt.mp hnot) with hlt | heq
  · have h := schoenfeldK_increasing X d v w hX0 hd0 hv0 hvden hlt hw1.le
    linarith
  · subst v
    linarith

end LeanLab.RieselVaughan1983.Task709
