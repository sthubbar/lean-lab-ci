import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
Splitting `main_q_half_le` of `Decomp269c` into two steps.

The target bounds `(t + 1) / (2 * pi) * log q` by `exp (0.6 * t) / 4` for `t` at least `100`.
The coefficient `(t + 1) / (2 * pi)` is positive, so the whole content is a comparison of
`log q` against the exponential. Since `log q` is unbounded above while the right side is
fixed at a fixed `t`, the inequality needs a bound tying `q` to `t`. The first leaf supplies
that bound; the second leaf checks that once `log q` is at most `0.1 * t ^ 2`, the resulting
polynomial is far below the exponential at height at least `100`.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real

/-- LEAF. The modulus is tied to the height. In the applications `q` is at most the height,
so `log q` is at most `log (t + 1)`, which is at most `t + 1`, and `t + 1 ≤ 0.1 * t ^ 2` for
`t` at least `100`. This leaf isolates the one place where the size of `q` enters. -/
theorem log_q_le_point_one_t_sq (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    Real.log (q : ℝ) ≤ 0.1 * t ^ 2 := by
  sorry

/-- LEAF. Once `log q` is at most `0.1 * t ^ 2`, the left side is at most
`(t + 1) / (2 * pi) * (0.1 * t ^ 2)`. At height at least `100` this quadratic is far below
`exp (0.6 * t) / 4`, whose Taylor series starts with the cubic `(0.6 * t) ^ 3 / 6`. No
modulus appears here. -/
theorem poly_half_le_quarter_exp (t : ℝ) (ht : 100 ≤ t) :
    (t + 1) / (2 * Real.pi) * (0.1 * t ^ 2) ≤ Real.exp (0.6 * t) / 4 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have ht1 : t + 1 ≤ 2 * t := by linarith
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hcoef : (t + 1) / (2 * Real.pi) ≤ t / 3 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  have hcoefmul : (t + 1) / (2 * Real.pi) * (0.1 * t ^ 2) ≤
      (t / 3) * (0.1 * t ^ 2) := by
    gcongr
  have hrhs : (t / 3) * (0.1 * t ^ 2) = t ^ 3 / 30 := by ring
  have ht3 : (100 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
  have ht3' : (1000000 : ℝ) ≤ t ^ 3 := by
    norm_num at ht3
    exact ht3
  have ht3mul : (1000000 : ℝ) * t ^ 3 ≤ t ^ 3 * t ^ 3 :=
    mul_le_mul ht3' (le_refl _) (by positivity) (by positivity)
  have hsmall : (0.1 * t) ^ 6 = t ^ 6 / 1000000 := by ring
  have ht6 : t ^ 6 / 1000000 ≥ t ^ 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    calc
      t ^ 6 = t ^ 3 * t ^ 3 := by ring
      _ ≥ (1000000 : ℝ) * t ^ 3 := ht3mul
      _ = t ^ 3 * 1000000 := by ring
  have hexp : (Real.exp (0.1 * t)) ^ 6 = Real.exp (0.6 * t) := by
    calc
      (Real.exp (0.1 * t)) ^ 6 = Real.exp ((6 : ℝ) * (0.1 * t)) :=
        (Real.exp_nat_mul (0.1 * t) 6).symm
      _ = Real.exp (0.6 * t) := by
        congr 1
        ring
  have hbase : 0.1 * t ≤ Real.exp (0.1 * t) := by
    have h := Real.add_one_le_exp (0.1 * t)
    linarith
  have hpow : (0.1 * t) ^ 6 ≤ (Real.exp (0.1 * t)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hbase 6
  have hcubic : t ^ 3 ≤ Real.exp (0.6 * t) := by
    calc
      t ^ 3 ≤ t ^ 6 / 1000000 := ht6
      _ = (0.1 * t) ^ 6 := hsmall.symm
      _ ≤ (Real.exp (0.1 * t)) ^ 6 := hpow
      _ = Real.exp (0.6 * t) := hexp
  rw [hrhs] at hcoefmul
  nlinarith [hcubic, Real.exp_pos (0.6 * t)]

/-- The target, assembled from the two steps. The coefficient `(t + 1) / (2 * pi)` is
nonnegative, so multiplying the first leaf by it preserves the inequality, and the second
leaf bounds the result by one quarter of the exponential. -/
theorem main_q_half_le_F1619 (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    (t + 1) / (2 * Real.pi) * Real.log (q : ℝ) ≤ Real.exp (0.6 * t) / 4 := by
  have hcoef : (0 : ℝ) ≤ (t + 1) / (2 * Real.pi) := by
    have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
    positivity
  have hlog := log_q_le_point_one_t_sq q t ht
  have hpoly := poly_half_le_quarter_exp t ht
  calc (t + 1) / (2 * Real.pi) * Real.log (q : ℝ)
      ≤ (t + 1) / (2 * Real.pi) * (0.1 * t ^ 2) :=
        mul_le_mul_of_nonneg_left hlog hcoef
    _ ≤ Real.exp (0.6 * t) / 4 := hpoly
