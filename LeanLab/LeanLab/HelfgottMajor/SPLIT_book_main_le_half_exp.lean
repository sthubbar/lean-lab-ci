import LeanLab.HelfgottMajor.SPLIT_zero_multiplicity_subexponential

/-!
Splitting `Decomp269c.book_main_le_half_exp` into three steps.

The target bounds the main term

`bookMain q (t + 1) = (t + 1) / (2 * pi) * log (q * (t + 1) / (2 * pi * e))`

by `exp (0.6 * t) / 2` for `t` at least `100`. The factor `(t + 1) / (2 * pi)` is harmless, so
the whole content is a comparison of two logarithms against the exponential: one carrying the
modulus and one carrying the height. Those are the second and the third leaf below, and the
first leaf is the split of the logarithm of the quotient, which removes the constant
`2 * pi * e`.

`bookMain` grows like `t * log q`, so the second leaf is a statement about the modulus: it holds
once `log q` is tied to `t` (for instance by `log q <= 0.1 * t ^ 2`, which is how the repair of
this step is stated elsewhere) and it fails for a modulus whose logarithm is larger than
`exp (0.6 * t) * pi / 2`, because `Real.log` is unbounded above and `t` is held fixed. Nothing in
the target's hypotheses ties `q` to `t`, so that comparison is the input this split isolates at
a single place; the assembly below is the two halves added.

`zero_multiplicity_subexponential` and `book_main_le_half_exp` itself are not used.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. Splitting the logarithm of the quotient. The argument
`q * (t + 1) / (2 * pi * e)` is a quotient of two positive numbers, so its logarithm is
`log (q * (t + 1)) - log (2 * pi * e)`, and `log (2 * pi * e)` is positive because `2 * pi > 1`.
Dropping that positive correction leaves `log q + log (t + 1)`, as both factors are positive.
This is the only place the constant `2 * pi * e` appears. -/
theorem log_arg_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    Real.log ((q : ℝ) * (t + 1) / (2 * Real.pi * Real.exp 1))
      ≤ Real.log (q : ℝ) + Real.log (t + 1) := by
  sorry

/-- LEAF. The modulus half of the exponential dominance. The coefficient `(t + 1) / (2 * pi)` is
positive, so this compares `log q` with `exp (0.6 * t)`. It is the one step that sees the
modulus, and it is where a bound tying `q` to `t` would be needed: `log q` is unbounded above
while the right side is fixed at a fixed `t`, so as a statement about every modulus it fails,
and it holds for a modulus with `log q <= 0.1 * t ^ 2` at height at least `100`. Nothing else in
the file refers to `q`. -/
theorem main_q_half_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    (t + 1) / (2 * Real.pi) * Real.log (q : ℝ) ≤ Real.exp (0.6 * t) / 4 := by
  sorry

/-- LEAF. The height half of the exponential dominance, with no modulus in it. The left side is
`(t + 1) / (2 * pi) * log (t + 1)`, which is at most `(t + 1) ^ 2 / (2 * pi)` because
`log y <= y` for `y >= 1`; at height at least `100` that quadratic is far below the exponential,
whose series starts with the cubic `(0.6 * t) ^ 3 / 6`. -/
theorem main_height_half_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    (t + 1) / (2 * Real.pi) * Real.log (t + 1) ≤ Real.exp (0.6 * t) / 4 := by
  sorry

/-- The target, assembled from the three steps. The main term is the coefficient times the
logarithm of the quotient; the first leaf bounds that logarithm by the sum of the two logarithms,
the coefficient is nonnegative so it is multiplied through, the two halves are the second and the
third leaf, and the two quarters add up to the half. -/
theorem book_main_le_half_exp_split (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    ZeroCount1623.bookMain q (t + 1) ≤ exp (0.6 * t) / 2 := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hpos : (0 : ℝ) ≤ (t + 1) / (2 * Real.pi) := div_nonneg ht1.le (by positivity)
  have hlog := log_arg_le q t ht
  have hq := main_q_half_le q t ht
  have hT := main_height_half_le q t ht
  have hmul := mul_le_mul_of_nonneg_left hlog hpos
  unfold ZeroCount1623.bookMain
  calc (t + 1) / (2 * Real.pi) *
        Real.log ((q : ℝ) * (t + 1) / (2 * Real.pi * Real.exp 1))
      ≤ (t + 1) / (2 * Real.pi) * (Real.log (q : ℝ) + Real.log (t + 1)) := hmul
    _ = (t + 1) / (2 * Real.pi) * Real.log (q : ℝ)
          + (t + 1) / (2 * Real.pi) * Real.log (t + 1) := by ring
    _ ≤ exp (0.6 * t) / 4 + exp (0.6 * t) / 4 := by linarith
    _ = exp (0.6 * t) / 2 := by ring
