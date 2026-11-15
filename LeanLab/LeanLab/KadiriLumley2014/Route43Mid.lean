/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Page 8 display 2.41, the sum S2 of Lemma 2.5, and page 9 display 2.58, the
coefficient B2 of Lemma 2.6, evaluated at Table 2 row 43:
m = 5, delta = 33490 / 10^12, u = delta / 5, T1 = 291316980, X near e^43.
The B2 summand of the envelope budget, times X^(-1/2), is bounded BELOW by 0.147 here,
with F standing for the higher factor of the weight at m = 5.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259

namespace LeanLab.KadiriLumley2014.Route43
open Real LeanLab.KadiriLumley2014.Task259

private lemma exp_one_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

/-- Page 8 display 2.41: the logarithm log(T1 / 2 pi) at T1 = 291316980 is at least 17.65. -/
private lemma logT_ge : (17.65 : ℝ) ≤ Real.log (291316980 / (2 * π)) := by
  have he0 := Real.exp_pos 1
  have h65 : Real.exp (13 / 20 : ℝ) < 1.9156 := by
    have h4 : Real.exp (13 / 20 : ℝ) ^ 20 = Real.exp 1 ^ 13 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 1 ^ 13 < (1.9156 : ℝ) ^ 20 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ exp_one_lt he0.le (by norm_num)) (by norm_num)
    rw [← h4] at h5
    exact lt_of_pow_lt_pow_left₀ 20 (by norm_num) h5
  have h17 : Real.exp (17 : ℝ) ≤ (2.7182818286 : ℝ) ^ 17 := by
    have : Real.exp (17 : ℝ) = Real.exp 1 ^ 17 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ he0.le exp_one_lt.le 17
  have hsplit : Real.exp (17.65 : ℝ) = Real.exp 17 * Real.exp (13 / 20) := by
    rw [← Real.exp_add]; norm_num
  have hexp : Real.exp (17.65 : ℝ) ≤ 291316980 / (2 * 3.1416) := by
    rw [hsplit]
    calc Real.exp 17 * Real.exp (13 / 20)
        ≤ (2.7182818286 : ℝ) ^ 17 * 1.9156 :=
          mul_le_mul h17 h65.le (Real.exp_pos _).le (by positivity)
      _ ≤ 291316980 / (2 * 3.1416) := by norm_num
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hle : (291316980 : ℝ) / (2 * 3.1416) ≤ 291316980 / (2 * π) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact hexp.trans hle

/-- Page 8 display 2.41: the logarithm log(H / 2 pi) at H = 30610000000 is at most 33. -/
private lemma logH_le : Real.log (30610000000 / (2 * π)) ≤ 33 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h33 : (2 : ℝ) ^ 33 ≤ Real.exp 33 := by
    have : Real.exp (33 : ℝ) = Real.exp 1 ^ 33 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) h2 33
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have : (30610000000 : ℝ) / (2 * π) ≤ 30610000000 / 6 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  exact this.trans (le_trans (by norm_num) h33)

/-- Page 8 display 2.41 at m = 5 and T1 = 291316980: S2 from below, dropping the
nonnegative q term and the nonnegative remainder term. -/
private lemma zeroS2_ge :
    (10000 / (2 * 31416) : ℝ) *
      ((1 + 5 * 17.65) / (25 * 291316980 ^ 5) - 166 / (25 * 30610000000 ^ 5)) ≤
      zeroS2 5 291316980 := by
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hL := logT_ge
  have hH := logH_le
  have hlogT : (1 : ℝ) ≤ Real.log 291316980 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans exp_one_lt.le (by norm_num)
  have hq : 0 ≤ countQ 291316980 := by
    unfold countQ
    apply div_nonneg
    · nlinarith
    · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hR : 0 ≤ countRemainder 291316980 := by
    unfold countRemainder
    have : 0 ≤ Real.log (Real.log 291316980) := Real.log_nonneg hlogT
    nlinarith
  have hA : (1 + 5 * 17.65) / (25 * 291316980 ^ 5) ≤
      (1 + ((5 : ℕ) : ℝ) * Real.log (291316980 / (2 * π))) /
        (((5 : ℕ) : ℝ) ^ 2 * 291316980 ^ 5) := by
    have : (((5 : ℕ) : ℝ) ^ 2 * 291316980 ^ 5) = 25 * 291316980 ^ 5 := by norm_num
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast; linarith
  have hB : (1 + ((5 : ℕ) : ℝ) * Real.log (30610000000 / (2 * π))) /
        (((5 : ℕ) : ℝ) ^ 2 * 30610000000 ^ 5) ≤ 166 / (25 * 30610000000 ^ 5) := by
    have : (((5 : ℕ) : ℝ) ^ 2 * 30610000000 ^ 5) = 25 * 30610000000 ^ 5 := by norm_num
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast; linarith
  have hD0 : (0 : ℝ) ≤
      (1 + 5 * 17.65) / (25 * 291316980 ^ 5) - 166 / (25 * 30610000000 ^ 5) := by
    norm_num
  have hpre : (10000 / (2 * 31416) : ℝ) ≤ 1 / (2 * π) + countQ 291316980 := by
    have : (10000 / (2 * 31416) : ℝ) ≤ 1 / (2 * π) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  have hlast : 0 ≤ 2 * countRemainder 291316980 / 291316980 ^ (5 + 1) := by positivity
  unfold zeroS2
  have hmul := mul_le_mul hpre (sub_le_sub hA hB) hD0 (le_trans (by norm_num) hpre)
  linarith

/-- The scalar exp(u/2) - 1 of page 9 display 2.58 at row 43, from above. -/
private lemma expm1_half_le {u : ℝ} (hu : u = 33490 / 10 ^ 12 / 5) :
    Real.exp (u / 2) - 1 ≤ 33490001 / 10 ^ 16 := by
  have h1 : 1 - u / 2 ≤ Real.exp (-(u / 2)) := by
    have := Real.add_one_le_exp (-(u / 2))
    linarith
  have hupos : (0 : ℝ) < 1 - u / 2 := by rw [hu]; norm_num
  have h2 : Real.exp (u / 2) ≤ 1 / (1 - u / 2) := by
    rw [Real.exp_neg] at h1
    have hepos := Real.exp_pos (u / 2)
    rw [le_div_iff₀ hupos]
    have := mul_le_mul_of_nonneg_left h1 hepos.le
    rw [mul_inv_cancel₀ hepos.ne'] at this
    linarith
  have : 1 / (1 - u / 2) ≤ 1 + 33490001 / 10 ^ 16 := by
    rw [div_le_iff₀ hupos, hu]; norm_num
  linarith

/-- The factor X^(-1/2) of the envelope budget at X at most e^43, from below. -/
private lemma rpow_neg_half_ge {X : ℝ} (hX0 : 0 < X) (hXhi : X ≤ Real.exp 43) :
    (1 / 2176100000 : ℝ) ≤ X ^ (-(1 / 2 : ℝ)) := by
  have he0 := Real.exp_pos 1
  have hhalf : Real.exp (1 / 2 : ℝ) < 1.64873 := by
    have h4 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 ^ 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 1 ^ 1 < (1.64873 : ℝ) ^ 2 := by
      rw [pow_one]; exact lt_of_lt_of_le exp_one_lt (by norm_num)
    rw [← h4] at h5
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h5
  have h21 : Real.exp (21 : ℝ) ≤ (2.7182818286 : ℝ) ^ 21 := by
    have : Real.exp (21 : ℝ) = Real.exp 1 ^ 21 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ he0.le exp_one_lt.le 21
  have hbig : Real.exp (43 / 2 : ℝ) ≤ 2176100000 := by
    have : Real.exp (43 / 2 : ℝ) = Real.exp 21 * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    calc Real.exp 21 * Real.exp (1 / 2)
        ≤ (2.7182818286 : ℝ) ^ 21 * 1.64873 :=
          mul_le_mul h21 hhalf.le (Real.exp_pos _).le (by positivity)
      _ ≤ 2176100000 := by norm_num
  have hlog : Real.log X ≤ 43 := (Real.log_le_iff_le_exp hX0).mpr hXhi
  have hge : Real.exp (-(43 / 2 : ℝ)) ≤ X ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : (1 / 2176100000 : ℝ) ≤ Real.exp (-(43 / 2 : ℝ)) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hbig
  exact hinv.trans hge

/-- Page 9 display 2.58, the coefficient B2 of Lemma 2.6 with S2 of page 8 display 2.41,
times X^(-1/2), at Table 2 row 43: m = 5, delta = 33490 / 10^12, u = delta / 5,
T1 = 291316980. Here F stands for the higher factor of the weight at m = 5. -/
theorem mid_term_ge {δ u X : ℝ} (hδ : δ = 33490 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : Real.exp 43 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ Real.exp 43) {F : ℝ}
    (hF : 84500 ≤ F) :
    (0.147 : ℝ) ≤ 2 * F / ((Real.exp (u / 2) - 1) * δ ^ 5) * zeroS2 5 291316980 *
      X ^ (-(1 / 2 : ℝ)) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  have hXp := rpow_neg_half_ge hX0 hXhi
  have hS := zeroS2_ge
  have hu' : u = 33490 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hE := expm1_half_le hu'
  have hEpos : 0 < Real.exp (u / 2) - 1 := by
    have : (0 : ℝ) < u / 2 := by rw [hu']; norm_num
    have := Real.add_one_lt_exp this.ne'
    linarith
  have hδ5 : (0 : ℝ) < δ ^ 5 := by rw [hδ]; positivity
  have hG : 2 * 84500 / ((33490001 / 10 ^ 16 : ℝ) * δ ^ 5) ≤
      2 * F / ((Real.exp (u / 2) - 1) * δ ^ 5) := by
    apply div_le_div₀ (by linarith) (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_right hE hδ5.le
  have hG0 : (0 : ℝ) ≤ 2 * 84500 / ((33490001 / 10 ^ 16 : ℝ) * δ ^ 5) := by positivity
  have hS0 : (0 : ℝ) ≤ (10000 / (2 * 31416) : ℝ) *
      ((1 + 5 * 17.65) / (25 * 291316980 ^ 5) - 166 / (25 * 30610000000 ^ 5)) := by
    norm_num
  have h1 := mul_le_mul hG hS hS0 (hG0.trans hG)
  have h2 := mul_le_mul h1 hXp (by norm_num) (le_trans (mul_nonneg hG0 hS0) h1)
  refine le_trans ?_ h2
  rw [hδ]
  norm_num

end LeanLab.KadiriLumley2014.Route43

#print axioms LeanLab.KadiriLumley2014.Route43.mid_term_ge
