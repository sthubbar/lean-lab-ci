/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Lemma 2.6 zero sum envelope: the terms B0 and B1 of displays 2.51 and 2.54,
with S1 of equation 2.40 and the zero count main term P and Rosser remainder R
of equation 2.32, evaluated at Table 2 row 1, threshold x0 = 4*10^18:
m = 5, delta = 35800 / 10^12, u = delta / 5, T1 = 272519712, X near 4*10^18.
The sum of B0 and B1 times X^(-1/2) is bounded BELOW by 0.7175 here.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259

namespace LeanLab.KadiriLumley2014.Route0
open Real
open LeanLab.KadiriLumley2014.Task259 LeanLab.KadiriLumley2014.Task92
  LeanLab.KadiriLumley2014.Task64

private lemma exp_nat (n : ℕ) : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
  rw [← Real.exp_nat_mul]; simp

private lemma exp_one_lt' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

private lemma exp_nat_le (n : ℕ) : Real.exp (n : ℝ) ≤ (2.7182818286 : ℝ) ^ n := by
  rw [exp_nat]
  exact pow_le_pow_left₀ (Real.exp_nonneg 1) exp_one_lt'.le n

private lemma two_pi_lo : (6.28 : ℝ) < 2 * π := by linarith [Real.pi_gt_d6]
private lemma two_pi_hi : 2 * π < (6.283186 : ℝ) := by linarith [Real.pi_lt_d6]

/-- Equation 2.32 remainder R is nonnegative at the Rosser height T0 = 1132491. -/
private lemma countRemainder_T0_nonneg : 0 ≤ countRemainder 1132491 := by
  have he : Real.exp 1 < (1132491 : ℝ) := Real.exp_one_lt_three.trans_le (by norm_num)
  have hlog : 1 < Real.log 1132491 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr he
  have hloglog : 0 < Real.log (Real.log 1132491) := Real.log_pos hlog
  unfold countRemainder
  nlinarith

/-- Equation 2.32 remainder R is nonnegative at T1 = 272519712. -/
private lemma countRemainder_T1_nonneg : 0 ≤ countRemainder 272519712 := by
  have he : Real.exp 1 < (272519712 : ℝ) := Real.exp_one_lt_three.trans_le (by norm_num)
  have hlog : 1 < Real.log 272519712 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr he
  have hloglog : 0 < Real.log (Real.log 272519712) := Real.log_pos hlog
  unfold countRemainder
  nlinarith

/-- The q function of equation 2.40 is nonnegative at T0 = 1132491. -/
private lemma countQ_T0_nonneg : 0 ≤ countQ 1132491 := by
  have h1 : 0 < Real.log 1132491 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log (1132491 / (2 * π)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith [two_pi_hi]
  unfold countQ
  positivity

/-- S1 of equation 2.40 at T1 = 272519712 is at least 10; its value is near 13.1. -/
private lemma zeroS1_ge : (10 : ℝ) ≤ zeroS1 272519712 := by
  have hπ : (0.15 : ℝ) ≤ 1 / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [two_pi_hi]
  have hL1 : (5 : ℝ) ≤ Real.log (272519712 / 1132491) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := exp_nat_le 5
    norm_num at this ⊢
    linarith
  have hsq : (17000000 : ℝ) ≤ Real.sqrt (272519712 * 1132491) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hL2 : (14 : ℝ) ≤ Real.log (Real.sqrt (272519712 * 1132491) / (2 * π)) := by
    have hpos : 0 < Real.sqrt (272519712 * 1132491) / (2 * π) := by
      apply div_pos (by linarith) (by positivity)
    rw [Real.le_log_iff_exp_le hpos, le_div_iff₀ (by positivity)]
    have h14 := exp_nat_le 14
    have h14' : Real.exp 14 ≤ 1300000 := by
      norm_num at h14 ⊢
      linarith
    have h0 : 0 ≤ Real.exp 14 := Real.exp_nonneg _
    nlinarith [two_pi_hi]
  have hq := countQ_T0_nonneg
  have hr := countRemainder_T0_nonneg
  have hmain : (10 : ℝ) ≤ (1 / (2 * π) + countQ 1132491) * Real.log (272519712 / 1132491) *
      Real.log (Real.sqrt (272519712 * 1132491) / (2 * π)) := by
    have ha : (0.15 : ℝ) ≤ 1 / (2 * π) + countQ 1132491 := by linarith
    have hb : (0.15 : ℝ) * 5 ≤ (1 / (2 * π) + countQ 1132491) *
        Real.log (272519712 / 1132491) :=
      mul_le_mul ha hL1 (by norm_num) (by linarith)
    have hc : (0.15 : ℝ) * 5 * 14 ≤ (1 / (2 * π) + countQ 1132491) *
        Real.log (272519712 / 1132491) *
        Real.log (Real.sqrt (272519712 * 1132491) / (2 * π)) :=
      mul_le_mul hb hL2 (by norm_num) (by linarith)
    linarith
  have hr' : 0 ≤ 2 * countRemainder 1132491 / 1132491 := by positivity
  unfold zeroS1
  linarith

private lemma exp_frac_le : Real.exp (29 / 50) ≤ 1.7861 := by
  by_contra h
  rw [not_le] at h
  have h1 : (1.7861 : ℝ) ^ 50 < Real.exp (29 / 50) ^ 50 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have h2 : Real.exp (29 / 50) ^ 50 = Real.exp 29 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 := exp_nat_le 29
  rw [h2] at h1
  norm_num at h1 h3
  linarith

/-- The zero count main term P of equation 2.32 at T1 = 272519712 is at least 719117000;
its value is near 719352000. -/
private lemma countMain_ge : (719117000 : ℝ) ≤ countMain 272519712 := by
  have hx : (43372580 : ℝ) ≤ 272519712 / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [two_pi_hi]
  have hlog : (17.58 : ℝ) ≤ Real.log (272519712 / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have hsplit : Real.exp (17.58 : ℝ) = Real.exp 17 * Real.exp (29 / 50) := by
      rw [← Real.exp_add]; norm_num
    have h17 := exp_nat_le 17
    have hf := exp_frac_le
    have hprod : Real.exp 17 * Real.exp (29 / 50) ≤ (2.7182818286 : ℝ) ^ 17 * 1.7861 := by
      apply mul_le_mul _ hf (Real.exp_nonneg _) (by positivity)
      exact_mod_cast h17
    rw [hsplit]
    refine le_trans hprod (le_trans ?_ hx)
    norm_num
  have hmul : (43372580 : ℝ) * 16.58 ≤
      272519712 / (2 * π) * (Real.log (272519712 / (2 * π)) - 1) :=
    mul_le_mul hx (by linarith) (by norm_num) (by linarith)
  unfold countMain
  nlinarith

/-- The power X^(-1/2) at X at most 4*10^18 is at least 1/(2*10^9). -/
private lemma xpow_ge {X : ℝ} (hXpos : 0 < X) (hXhi : X ≤ 4 * 10 ^ 18) :
    (1 / 2000000000 : ℝ) ≤ X ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hXpos.le, ← Real.sqrt_eq_rpow, one_div]
  apply inv_anti₀ (Real.sqrt_pos.mpr hXpos)
  have h1 : Real.sqrt X ≤ Real.sqrt ((2000000000 : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num; linarith)
  rwa [Real.sqrt_sq (by norm_num)] at h1

/-- P0059 Lemma 2.6: the terms B0 of display 2.51 and B1 of display 2.54 in the Rosser zero
envelope, with S1 of equation 2.40 and the count terms of equation 2.32, at Table 2 row 1,
x0 = 4*10^18, times X^(-1/2), are at least 0.7175. The value is near 0.719354. -/
theorem low_terms_ge {δ u X : ℝ} (hδ : δ = 35800 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : 4 * 10 ^ 18 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ 4 * 10 ^ 18) :
    (0.7175 : ℝ) ≤
      (min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * 11.637732363)
          (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) * 2001052) +
        min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * zeroS1 272519712)
          (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) *
            (countMain 272519712 + countRemainder 272519712 - 2001052))) *
        X ^ (-(1 / 2 : ℝ)) := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδle : δ ≤ 35800 / 10 ^ 12 := hδ.le
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  -- the exponential factor
  have hE1 : 1 ≤ Real.exp (u / 2) := by
    apply Real.one_le_exp
    rw [hu]; linarith
  have hE2 : Real.exp (u / 2) ≤ 1.00000002 := by
    have hneg : 1 - u / 2 ≤ Real.exp (-(u / 2)) := by
      have := Real.add_one_le_exp (-(u / 2))
      linarith
    rw [Real.exp_neg] at hneg
    have hup : u / 2 ≤ 1 / 10 ^ 8 := by rw [hu, hδ]; norm_num
    have hpos : 0 < Real.exp (u / 2) := Real.exp_pos _
    have h1 : (1 - 1 / 10 ^ 8 : ℝ) ≤ (Real.exp (u / 2))⁻¹ := by linarith
    have h2 : (1 - 1 / 10 ^ 8 : ℝ) * Real.exp (u / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    nlinarith
  have hDpos : 0 < Real.exp (u / 2) + 1 := by linarith
  -- the coefficient of the second branches
  have hC : (1.9999999 : ℝ) ≤ 4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) := by
    rw [le_div_iff₀ hDpos]
    nlinarith
  -- the coefficient of the first branches
  have hF : (5 : ℝ) ≤ firstFactor 5 δ := by
    refine le_trans ?_ (first_factor_bounds (by norm_num : 0 < 5) hδpos.le).1
    norm_num [lambdaZero, Nat.factorial]
  have hA : (270000000 : ℝ) ≤ 4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (Real.exp (u / 2) + 1) * δ ≤ 2.00000002 * (35800 / 10 ^ 12) :=
      mul_le_mul (by linarith) hδle hδpos.le (by norm_num)
    nlinarith
  have hS := zeroS1_ge
  have hM := countMain_ge
  have hR := countRemainder_T1_nonneg
  have hmin1 : (1.9999999 : ℝ) * 2001052 ≤
      min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * 11.637732363)
        (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) * 2001052) := by
    apply le_min
    · nlinarith
    · nlinarith
  have hmin2 : (1.9999999 : ℝ) * (719117000 - 2001052) ≤
      min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * zeroS1 272519712)
        (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) *
          (countMain 272519712 + countRemainder 272519712 - 2001052)) := by
    apply le_min
    · have : (270000000 : ℝ) * 10 ≤
          4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * zeroS1 272519712 :=
        mul_le_mul hA hS (by norm_num) (by linarith)
      linarith
    · exact mul_le_mul hC (by linarith) (by norm_num) (by linarith)
  have hXpow := xpow_ge hXpos hXhi
  have hsum : (1.9999999 : ℝ) * 719117000 ≤
      min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * 11.637732363)
          (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) * 2001052) +
        min (4 * firstFactor 5 δ / ((Real.exp (u / 2) + 1) * δ) * zeroS1 272519712)
          (4 * (1 + δ / 2) / (Real.exp (u / 2) + 1) *
            (countMain 272519712 + countRemainder 272519712 - 2001052)) := by
    linarith
  have hfin := mul_le_mul hsum hXpow (by norm_num) (by linarith)
  refine le_trans ?_ hfin
  norm_num

end LeanLab.KadiriLumley2014.Route0

#print axioms LeanLab.KadiriLumley2014.Route0.low_terms_ge
