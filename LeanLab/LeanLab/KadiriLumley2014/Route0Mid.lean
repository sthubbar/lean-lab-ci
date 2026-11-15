/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Page 8 display 2.41, the sum S2 of Lemma 2.5, and page 9 display 2.58, the
coefficient B2 of Lemma 2.6, evaluated at Table 2 row 1, the first row:
x0 = 4 * 10^18, m = 5, delta = 35800 / 10^12, u = delta / 5, T1 = 272519712,
X between 4 * 10^18 / (1 + 1/10^6) and 4 * 10^18.
The B2 summand of the envelope budget, times X^(-1/2), is bounded BELOW by 0.1530 here,
with F standing for the higher factor of the weight at m = 5.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259

namespace LeanLab.KadiriLumley2014.Route0
open Real LeanLab.KadiriLumley2014.Task259

private lemma exp_one_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

/-- Page 8 display 2.41: the logarithm log(T1 / 2 pi) at T1 = 272519712 is at least 17.58. -/
private lemma logT_ge : (17.58 : ℝ) ≤ Real.log (272519712 / (2 * π)) := by
  have he0 := Real.exp_pos 1
  have h58 : Real.exp (29 / 50 : ℝ) < 1.78604 := by
    have h4 : Real.exp (29 / 50 : ℝ) ^ 50 = Real.exp 1 ^ 29 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 1 ^ 29 < (1.78604 : ℝ) ^ 50 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ exp_one_lt he0.le (by norm_num)) (by norm_num)
    rw [← h4] at h5
    exact lt_of_pow_lt_pow_left₀ 50 (by norm_num) h5
  have h17 : Real.exp (17 : ℝ) ≤ (2.7182818286 : ℝ) ^ 17 := by
    have : Real.exp (17 : ℝ) = Real.exp 1 ^ 17 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ he0.le exp_one_lt.le 17
  have hsplit : Real.exp (17.58 : ℝ) = Real.exp 17 * Real.exp (29 / 50) := by
    rw [← Real.exp_add]; norm_num
  have hexp : Real.exp (17.58 : ℝ) ≤ 272519712 / (2 * 3.141593) := by
    rw [hsplit]
    calc Real.exp 17 * Real.exp (29 / 50)
        ≤ (2.7182818286 : ℝ) ^ 17 * 1.78604 :=
          mul_le_mul h17 h58.le (Real.exp_pos _).le (by positivity)
      _ ≤ 272519712 / (2 * 3.141593) := by norm_num
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hle : (272519712 : ℝ) / (2 * 3.141593) ≤ 272519712 / (2 * π) := by
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

/-- Page 8 display 2.41 at m = 5 and T1 = 272519712: S2 from below, dropping the
nonnegative q term and the nonnegative remainder term. -/
private lemma zeroS2_ge :
    (1000000 / (2 * 3141593) : ℝ) *
      ((1 + 5 * 17.58) / (25 * 272519712 ^ 5) - 166 / (25 * 30610000000 ^ 5)) ≤
      zeroS2 5 272519712 := by
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hL := logT_ge
  have hH := logH_le
  have hlogT : (1 : ℝ) ≤ Real.log 272519712 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans exp_one_lt.le (by norm_num)
  have hq : 0 ≤ countQ 272519712 := by
    unfold countQ
    apply div_nonneg
    · nlinarith
    · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hR : 0 ≤ countRemainder 272519712 := by
    unfold countRemainder
    have : 0 ≤ Real.log (Real.log 272519712) := Real.log_nonneg hlogT
    nlinarith
  have hA : (1 + 5 * 17.58) / (25 * 272519712 ^ 5) ≤
      (1 + ((5 : ℕ) : ℝ) * Real.log (272519712 / (2 * π))) /
        (((5 : ℕ) : ℝ) ^ 2 * 272519712 ^ 5) := by
    have : (((5 : ℕ) : ℝ) ^ 2 * 272519712 ^ 5) = 25 * 272519712 ^ 5 := by norm_num
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
      (1 + 5 * 17.58) / (25 * 272519712 ^ 5) - 166 / (25 * 30610000000 ^ 5) := by
    norm_num
  have hpre : (1000000 / (2 * 3141593) : ℝ) ≤ 1 / (2 * π) + countQ 272519712 := by
    have : (1000000 / (2 * 3141593) : ℝ) ≤ 1 / (2 * π) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  have hlast : 0 ≤ 2 * countRemainder 272519712 / 272519712 ^ (5 + 1) := by positivity
  unfold zeroS2
  have hmul := mul_le_mul hpre (sub_le_sub hA hB) hD0 (le_trans (by norm_num) hpre)
  linarith

/-- The scalar exp(u/2) - 1 of page 9 display 2.58 at row 1, from above. -/
private lemma expm1_half_le {u : ℝ} (hu : u = 35800 / 10 ^ 12 / 5) :
    Real.exp (u / 2) - 1 ≤ 358000002 / 10 ^ 17 := by
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
  have : 1 / (1 - u / 2) ≤ 1 + 358000002 / 10 ^ 17 := by
    rw [div_le_iff₀ hupos, hu]; norm_num
  linarith

/-- The factor X^(-1/2) of the envelope budget at X at most 4 * 10^18, from below,
using sqrt(4 * 10^18) = 2 * 10^9. -/
private lemma rpow_neg_half_ge {X : ℝ} (hX0 : 0 < X) (hXhi : X ≤ 4 * 10 ^ 18) :
    (1 / (2 * 10 ^ 9) : ℝ) ≤ X ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hX0.le, ← Real.sqrt_eq_rpow, one_div]
  have hs : Real.sqrt X ≤ 2 * 10 ^ 9 := by
    have h4 : (4 * 10 ^ 18 : ℝ) = (2 * 10 ^ 9) ^ 2 := by norm_num
    calc Real.sqrt X ≤ Real.sqrt (4 * 10 ^ 18) := Real.sqrt_le_sqrt hXhi
      _ = 2 * 10 ^ 9 := by rw [h4, Real.sqrt_sq (by norm_num)]
  exact inv_anti₀ (Real.sqrt_pos.mpr hX0) hs

/-- Page 9 display 2.58, the coefficient B2 of Lemma 2.6 with S2 of page 8 display 2.41,
times X^(-1/2), at Table 2 row 1: x0 = 4 * 10^18, m = 5, delta = 35800 / 10^12,
u = delta / 5, T1 = 272519712. Here F stands for the higher factor of the weight at m = 5. -/
theorem mid_term_ge {δ u X : ℝ} (hδ : δ = 35800 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : 4 * 10 ^ 18 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ 4 * 10 ^ 18) {F : ℝ}
    (hF : 86200 ≤ F) :
    (0.1530 : ℝ) ≤ 2 * F / ((Real.exp (u / 2) - 1) * δ ^ 5) * zeroS2 5 272519712 *
      X ^ (-(1 / 2 : ℝ)) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  have hXp := rpow_neg_half_ge hX0 hXhi
  have hS := zeroS2_ge
  have hu' : u = 35800 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hE := expm1_half_le hu'
  have hEpos : 0 < Real.exp (u / 2) - 1 := by
    have : (0 : ℝ) < u / 2 := by rw [hu']; norm_num
    have := Real.add_one_lt_exp this.ne'
    linarith
  have hδ5 : (0 : ℝ) < δ ^ 5 := by rw [hδ]; positivity
  have hG : 2 * 86200 / ((358000002 / 10 ^ 17 : ℝ) * δ ^ 5) ≤
      2 * F / ((Real.exp (u / 2) - 1) * δ ^ 5) := by
    apply div_le_div₀ (by linarith) (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_right hE hδ5.le
  have hG0 : (0 : ℝ) ≤ 2 * 86200 / ((358000002 / 10 ^ 17 : ℝ) * δ ^ 5) := by positivity
  have hS0 : (0 : ℝ) ≤ (1000000 / (2 * 3141593) : ℝ) *
      ((1 + 5 * 17.58) / (25 * 272519712 ^ 5) - 166 / (25 * 30610000000 ^ 5)) := by
    norm_num
  have h1 := mul_le_mul hG hS hS0 (hG0.trans hG)
  have h2 := mul_le_mul h1 hXp (by norm_num) (le_trans (mul_nonneg hG0 hS0) h1)
  refine le_trans ?_ h2
  rw [hδ]
  norm_num

end LeanLab.KadiriLumley2014.Route0

#print axioms LeanLab.KadiriLumley2014.Route0.mid_term_ge
