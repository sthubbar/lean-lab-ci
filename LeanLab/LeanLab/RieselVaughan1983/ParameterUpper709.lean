import LeanLab.RieselVaughan1983.ParameterRoot709
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
The upper logarithmic trial point in Schoenfeld 1976 page 345 equation 7.29.
Mathlib supplies the monotonicity of log x divided by sqrt x.
The explicit zero-sum bounds remain separate.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Set

namespace LeanLab.RieselVaughan1983.Task709

/-- Domain and exponent bounds for the second trial point in equation 7.29.
The rational constants are auxiliary sufficient bounds for the tail. -/
theorem schoenfeld_second_trial_bounds (X : ℝ) (hX : 14 ≤ X) :
    let q := 17 * X / (5 * Real.pi)
    25 / 28 < 1 - log q / (2 * X) ∧ log q ^ 2 / X < 9 / 14 := by
  let q : ℝ := 17 * X / (5 * Real.pi)
  let q0 : ℝ := 17 * 14 / (5 * Real.pi)
  have hX0 : 0 < X := by linarith
  have hq08 : 8 < q0 := by
    dsimp [q0]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hq016 : q0 < 16 := by
    dsimp [q0]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hqq : q0 ≤ q := by
    dsimp [q0, q]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hq00 : 0 < q0 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have he2 : exp (2 : ℝ) < 8 := by
    calc
      _ = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (2.7182818286 : ℝ) ^ 2 := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 2
      _ < 8 := by norm_num
  have he3 : (16 : ℝ) < exp 3 := by
    calc
      _ < (2.7182818283 : ℝ) ^ 3 := by norm_num
      _ ≤ exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 3
      _ = exp 3 := by rw [← exp_nat_mul]; norm_num
  have hlog03 : log q0 < 3 := (log_lt_iff_lt_exp hq00).mpr (hq016.trans he3)
  have hlog00 : 0 ≤ log q0 := log_nonneg (by linarith)
  have hlogq0 : 0 ≤ log q := log_nonneg hq1
  have hsplit : log q = log (X / 14) + log q0 := by
    rw [← log_mul (by positivity : X / 14 ≠ 0) hq00.ne']
    congr 1
    dsimp [q, q0]
    field_simp [Real.pi_ne_zero]
  have htangent := log_le_sub_one_of_pos (show 0 < X / 14 by positivity)
  have hlog : log q < 3 / 14 * X := by rw [hsplit]; linarith
  have hdiv : log q / (2 * X) < 3 / 28 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * X)).mpr
    linarith
  have hmono := Real.log_div_sqrt_antitoneOn
    (show q0 ∈ Ici (exp 2) from (he2.trans hq08).le)
    (show q ∈ Ici (exp 2) from (he2.trans hq08).le.trans hqq) hqq
  have hsq := pow_le_pow_left₀
    (by positivity : 0 ≤ log q / sqrt q) hmono 2
  rw [div_pow, div_pow, sq_sqrt hq0.le, sq_sqrt hq00.le] at hsq
  have hscaled : log q ^ 2 / X ≤ log q0 ^ 2 / 14 := by
    have h := mul_le_mul_of_nonneg_right hsq
      (show (0 : ℝ) ≤ 17 / (5 * Real.pi) by positivity)
    convert h using 1 <;> dsimp [q, q0] <;>
      field_simp [hX0.ne', Real.pi_ne_zero]
  have hsq03 : log q0 ^ 2 < 9 := by
    nlinarith [mul_pos (sub_pos.mpr hlog03) (show 0 < 3 + log q0 by linarith)]
  exact ⟨by linarith, hscaled.trans_lt (div_lt_div_of_pos_right hsq03 (by norm_num))⟩

/-- The upper root localization in equation 7.30 on page 345,
restricted to the tail X at least 14 used by the assigned source leaf. -/
theorem schoenfeld_root_lt_second_trial (X v : ℝ) (hX : 14 ≤ X)
    (hv : v ∈ Ioo (sqrt (1 / 2)) 1)
    (hroot : schoenfeldK X (log (17 / (2 * Real.pi))) v = 1) :
    v < 1 - log (17 * X / (5 * Real.pi)) / (2 * X) := by
  let d : ℝ := log (17 / (2 * Real.pi))
  let q : ℝ := 17 * X / (5 * Real.pi)
  let w : ℝ := 1 - log q / (2 * X)
  have hX0 : 0 < X := by linarith
  have hd : (1 / 4 : ℝ) ≤ d := by
    have htwo : (2 : ℝ) ≤ 17 / (2 * Real.pi) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      nlinarith [Real.pi_lt_four]
    have h := log_le_log (by norm_num : (0 : ℝ) < 2) htwo
    dsimp [d]
    linarith [Real.log_two_gt_d9]
  have hd0 : 0 ≤ d := by linarith
  have hs : 25 / 28 < w ∧ log q ^ 2 / X < 9 / 14 := schoenfeld_second_trial_bounds X hX
  have hwlo := hs.1
  have hw0 : 0 < w := by linarith
  have hq1 : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  have hw1 : w < 1 := by
    have hp := div_pos (log_pos hq1) (show 0 < 2 * X by positivity)
    dsimp [w]
    linarith
  have hwden : 1 < 2 * w ^ 2 := by nlinarith [sq_nonneg (w - 25 / 28)]
  have hH := schoenfeldH_bounds X d w hX0 hd hw0 hwden hw1.le
  have hp6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 25 / 28) hwlo.le 6
  have hp2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 25 / 28) hwlo.le 2
  have hprod : (25 / 28 : ℝ) ^ 6 * (2 * (25 / 28 : ℝ) ^ 2 - 1) ≤
      w ^ 6 * (2 * w ^ 2 - 1) :=
    mul_le_mul hp6 (by linarith) (by norm_num) (by positivity)
  have hHquarter : (1 / 4 : ℝ) < schoenfeldH X d w := by
    have hrat : (1 / 4 : ℝ) < (25 / 28 : ℝ) ^ 6 * (2 * (25 / 28 : ℝ) ^ 2 - 1) :=
      by norm_num
    exact (hrat.trans_le hprod).trans hH.1
  have hsqrt : (1 / 2 : ℝ) < sqrt (schoenfeldH X d w) := by
    apply (lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    linarith
  have hbudget : log q ^ 2 / (4 * w * X) < 1 / 5 := by
    have hqbound := (div_lt_iff₀ hX0).mp hs.2
    have hwX := mul_lt_mul_of_pos_right hwlo hX0
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * w * X)).mpr
    nlinarith
  have hexp : (4 / 5 : ℝ) < exp (-(log q) ^ 2 / (4 * w * X)) := by
    have h := add_one_le_exp (-(log q) ^ 2 / (4 * w * X))
    have heq : -(log q) ^ 2 / (4 * w * X) = -(log q ^ 2 / (4 * w * X)) := by ring
    rw [heq] at h ⊢
    linarith
  have heval : schoenfeldK X d w = 5 / 2 * sqrt (schoenfeldH X d w) *
      exp (-(log q) ^ 2 / (4 * w * X)) := by
    simpa only using schoenfeldK_at_log_parameter X 5 d hX0 (by norm_num) hw0
  have hKw : 1 < schoenfeldK X d w := by
    rw [heval]
    calc
      _ = (5 / 2 : ℝ) * (1 / 2) * (4 / 5) := by norm_num
      _ < _ := by gcongr
  have hv0 : 0 < v := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans hv.1
  have hvden : 1 < 2 * v ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hv.1)
      (show 0 < v + sqrt (1 / 2) by positivity)
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  change schoenfeldK X d v = 1 at hroot
  change v < w
  by_contra hnot
  rcases lt_or_eq_of_le (not_lt.mp hnot) with hlt | heq
  · have h := schoenfeldK_increasing X d w v hX0 hd0 hw0 hwden hlt hv.2.le
    linarith
  · subst v
    linarith

end LeanLab.RieselVaughan1983.Task709
