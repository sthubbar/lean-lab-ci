import LeanLab.HelfgottMajor.SPLIT_book_main_le_half_exp

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
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

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
  sorry

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
