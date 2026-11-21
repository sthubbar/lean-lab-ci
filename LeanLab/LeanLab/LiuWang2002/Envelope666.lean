import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
A scalar obstruction to using only the Axler absolute error envelope.
Derived proof bookkeeping for Schoenfeld 1976 page 356 display 5.1 star.
The point 32000001 is the first integer of the assigned c6 range.
This is not a claim that a paper theorem fails.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task666

/-- The Axler error envelope alone does not imply the primorial logarithmic target. -/
theorem axler_envelope_insufficient (X : ℝ) (hX : 1 < X) (hTop : X ≤ 32000001) :
    ¬ (∀ T : ℝ, |T - X| < 100 * X / Real.log X ^ 4 →
      T < X * Real.log (68 / 25)) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsmall : (1.0007 : ℝ) ≤ Real.exp 0.0007 := by
    calc (1.0007 : ℝ) = 0.0007 + 1 := by norm_num
      _ ≤ Real.exp 0.0007 := Real.add_one_le_exp _
  have hratio : Real.log (68 / 25 : ℝ) < 1.0007 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 68 / 25)).2
    calc (68 / 25 : ℝ) < 2.7182818283 * 1.0007 := by norm_num
      _ < Real.exp 1 * Real.exp 0.0007 := by
        have hm := mul_lt_mul_of_pos_right he (by norm_num : (0 : ℝ) < 1.0007)
        exact hm.trans_le (mul_le_mul_of_nonneg_left hsmall (Real.exp_pos 1).le)
      _ = Real.exp 1.0007 := by rw [← Real.exp_add]; norm_num
  have hexp : (32000001 : ℝ) < Real.exp 18 := by
    have hpow := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      (by decide : (18 : ℕ) ≠ 0)
    have hid : Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid]
    exact lt_trans (by norm_num) hpow
  have hX0 : 0 < X := lt_trans (by norm_num) hX
  have hlog : Real.log X < 18 :=
    (Real.log_lt_iff_lt_exp hX0).2 (hTop.trans_lt hexp)
  have hlog0 : 0 < Real.log X := Real.log_pos hX
  have hpow : Real.log X ^ 4 < (18 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hlog hlog0.le (by decide)
  have herr : (0.0008 : ℝ) < 100 / Real.log X ^ 4 := by
    apply lt_trans (show (0.0008 : ℝ) < 100 / (18 : ℝ) ^ 4 by norm_num)
    exact div_lt_div_of_pos_left (by norm_num) (pow_pos hlog0 4) hpow
  intro h
  have hdomain : |(1.0008 : ℝ) * X - X| < 100 * X / Real.log X ^ 4 := by
    calc |(1.0008 : ℝ) * X - X| = 0.0008 * X := by
          rw [show (1.0008 : ℝ) * X - X = 0.0008 * X by ring,
            abs_of_nonneg (by positivity)]
      _ < (100 / Real.log X ^ 4) * X := mul_lt_mul_of_pos_right herr hX0
      _ = 100 * X / Real.log X ^ 4 := by ring
  have hbad := h (1.0008 * X) hdomain
  have hr := mul_lt_mul_of_pos_left hratio hX0
  nlinarith only [hbad, hr, hX0]

end LeanLab.LiuWang2002.Task666
#print axioms LeanLab.LiuWang2002.Task666.axler_envelope_insufficient
