import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
Elementary parameter comparisons in the written proof of Schoenfeld Theorem 11.
Sources: Schoenfeld 1976 pages 343 and 345, equations 7.12, 7.25, 7.27 and 7.28.
These comparisons prove no psi estimate by themselves.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.Task426

/-- The G0 polynomial of equation 7.12 is increasing on positive arguments.
The parameter b is d divided by X in the paper. -/
theorem schoenfeld_G0_increasing {b v w : ℝ} (hb : 0 ≤ b) (hv : 0 < v) (hvw : v < w) :
    v ^ 2 * (v + b) < w ^ 2 * (w + b) := by
  have hp : v ^ 2 < w ^ 2 := pow_lt_pow_left₀ hvw hv.le (by decide : (2 : ℕ) ≠ 0)
  calc v ^ 2 * (v + b) < w ^ 2 * (v + b) :=
      mul_lt_mul_of_pos_right hp (by linarith)
    _ ≤ w ^ 2 * (w + b) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

/-- The G1 rational function of equation 7.25 decreases on the whole interval
used in the page 345 monotonicity assertion. Here a is the nonnegative parameter
the quotient of the sum 1 plus 2 d by 2 X. The squared endpoint avoids a square root convention. -/
theorem schoenfeld_G1_decreasing {a v w : ℝ} (ha : 0 ≤ a) (hv : 0 < v)
    (hden : 1 < 2 * v ^ 2) (hvw : v < w) (hw : w ^ 2 ≤ 3 / 2) :
    w ^ 2 * (w + a) / (2 * w ^ 2 - 1) <
      v ^ 2 * (v + a) / (2 * v ^ 2 - 1) := by
  have hw0 : 0 < w := hv.trans hvw
  have hdv : 0 < 2 * v ^ 2 - 1 := by linarith
  have hdw : 0 < 2 * w ^ 2 - 1 := by nlinarith
  have hfactor : 0 < v ^ 2 + w ^ 2 + v * w - 2 * v ^ 2 * w ^ 2 + a * (v + w) := by
    have hs := mul_nonneg (sq_nonneg v) (show 0 ≤ 3 - 2 * w ^ 2 by linarith)
    have hg := mul_pos (sub_pos.mpr hvw) (show 0 < w + 2 * v by linarith)
    have ha' := mul_nonneg ha (show 0 ≤ v + w by linarith)
    nlinarith
  have hp := mul_pos (sub_pos.mpr hvw) hfactor
  rw [div_lt_div_iff₀ hdw hdv]
  nlinarith only [hp]

/-- The ratio G0 cubed divided by G1 in equation 7.28 is increasing.
Both parameters are left general and nonnegative. -/
theorem schoenfeld_H_increasing {a b v w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : 0 < v) (hden : 1 < 2 * v ^ 2) (hvw : v < w) (hw : w ^ 2 ≤ 3 / 2) :
    (v ^ 2 * (v + b)) ^ 3 / (v ^ 2 * (v + a) / (2 * v ^ 2 - 1)) <
      (w ^ 2 * (w + b)) ^ 3 / (w ^ 2 * (w + a) / (2 * w ^ 2 - 1)) := by
  have hw0 : 0 < w := hv.trans hvw
  have hdv : 0 < 2 * v ^ 2 - 1 := by linarith
  have hdw : 0 < 2 * w ^ 2 - 1 := by nlinarith
  have hGv : 0 < v ^ 2 * (v + a) / (2 * v ^ 2 - 1) := by positivity
  have hGw : 0 < w ^ 2 * (w + a) / (2 * w ^ 2 - 1) := by positivity
  have hnv : 0 ≤ v ^ 2 * (v + b) := by positivity
  have hnw : 0 ≤ (w ^ 2 * (w + b)) ^ 3 := by positivity
  have hnum := pow_lt_pow_left₀ (schoenfeld_G0_increasing hb hv hvw) hnv
    (by decide : (3 : ℕ) ≠ 0)
  have hdiv := schoenfeld_G1_decreasing ha hv hden hvw hw
  exact (div_lt_div_of_pos_right hnum hGv).trans_le
    (div_le_div_of_nonneg_left hnw hGw hdiv.le)

/-- The final exponent kernel in equation 7.27 decreases on the positive unit interval.
For positive X its negative X multiple therefore gives an increasing exponential factor. -/
theorem schoenfeld_exponent_kernel_decreasing {v w : ℝ} (hv : 0 < v)
    (hvw : v < w) (hw : w ≤ 1) :
    (1 - w) ^ 2 / w < (1 - v) ^ 2 / v := by
  have hw0 : 0 < w := hv.trans hvw
  have hprod : v * w < 1 := by
    calc v * w ≤ v * 1 := mul_le_mul_of_nonneg_left hw hv.le
      _ < 1 := by linarith
  have hp := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr hprod)
  rw [div_lt_div_iff₀ hw0 hv]
  nlinarith only [hp]

/-- The upper endpoint k at 1 exceeds 1, as asserted after equation 7.27
on page 345. The paper defines d as the logarithm of the quotient of 17 by 2 pi.
The stronger parameter family d nonnegative also works. -/
theorem schoenfeld_k_one_gt_one (X d : ℝ) (hX : 1 ≤ X) (hd : 0 ≤ d) :
    1 < (17 * X / (2 * Real.pi)) *
      Real.sqrt ((1 + d / X) ^ 3 / (1 + (1 + 2 * d) / (2 * X))) := by
  have hX0 : 0 < X := by linarith
  let a : ℝ := 1 + d / X
  let D : ℝ := 1 + (1 + 2 * d) / (2 * X)
  have ha : 1 ≤ a := by
    have hnonneg : 0 ≤ d / X := div_nonneg hd hX0.le
    dsimp [a]
    linarith
  have ha0 : 0 < a := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hDdef : D = a + 1 / (2 * X) := by
    dsimp [D, a]
    field_simp
    ring
  have hhalf : 1 / (2 * X) ≤ (1 / 2 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hD : D ≤ (3 / 2 : ℝ) * a := by rw [hDdef]; linarith
  have ha3 : a ≤ a ^ 3 := by
    calc a = a * 1 := by ring
      _ ≤ a * a ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) ha0.le
      _ = a ^ 3 := by ring
  have hratio : (1 / 4 : ℝ) ≤ a ^ 3 / D := by
    apply (le_div_iff₀ hD0).mpr
    nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (a ^ 3 / D) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
    exact hratio
  have hcoef : 2 < 17 * X / (2 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    nlinarith [Real.pi_lt_four]
  change 1 < (17 * X / (2 * Real.pi)) * Real.sqrt (a ^ 3 / D)
  calc (1 : ℝ) = 2 * (1 / 2) := by ring
    _ < (17 * X / (2 * Real.pi)) * (1 / 2) :=
      mul_lt_mul_of_pos_right hcoef (by norm_num)
    _ ≤ (17 * X / (2 * Real.pi)) * Real.sqrt (a ^ 3 / D) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)

end LeanLab.RieselVaughan1983.Task426
