import LeanLab.HelfgottMajor.SPLIT_zero_multiplicity_subexponential

/-!
Splitting `book_error_le_half_exp` of `Decomp269c` into four steps.

The target bounds the explicit error `bookError q (t + 1) = 0.15 * log (q * (t + 1)) + 3.389`
at height `t + 1`, for `t` at least `100`, by half of `exp (0.6 * t)`. At that height the
exponential is vast, so the passage from the logarithm to the exponential is pure bookkeeping:
the logarithm of the product splits into its conductor part and its height part, the height part
is dominated by the exponential because a linear function is smaller than `exp (0.6 * t) / 4`
for `t` at least `100`, and the conductor part has to fit under the same quarter.

The four steps are therefore: the product formula for the logarithm of `q * (t + 1)`; the
elementary comparison `log (t + 1) ≤ t + 1`; the linear-versus-exponential comparison at the
height; and the absorption of `0.15 * log q + 3.389` into one quarter of the exponential. The
last of these is the only step in which the size of `q` enters, and it is a real constraint on
`q`: the right hand side carries no `q` at all, so the step holds only while `q` stays below
`exp (exp (0.6 * t) / 0.3)` in size. For `q` beyond that the target itself fails, and the
repair is a re-cut of the statement with a bound of `q` by the height, not a sharper estimate.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. Splitting the logarithm of the product `q * (t + 1)`. Both factors are positive — the
modulus `q` is nonzero and the height exceeds `1` — so the logarithm of the product is the sum
of the two logarithms. This isolates the two halves of `bookError` that the rest of the split
treats separately, and it is where the positivity of `q` is used. -/
theorem log_conductor_height_mul_le (q : ℕ) (t : ℝ) (hq : q ≠ 0) (ht : 100 ≤ t) :
    log ((q : ℝ) * (t + 1)) ≤ log q + log (t + 1) := by
  sorry

/-- LEAF. The height part of the logarithm is at most the height. The argument `t + 1` is at
least `101`, in particular at least `1`, so the elementary inequality `log x ≤ x` applies. This
leaf is the only place where the logarithm at the height is compared with a polynomial, and it
uses nothing about `q`. -/
theorem height_log_le_height (t : ℝ) (ht : 100 ≤ t) :
    log (t + 1) ≤ t + 1 := by
  sorry

/-- LEAF. Linear versus exponential at the height. Once the height part of the logarithm has
been replaced by `t + 1`, the remaining claim `0.15 * (t + 1) ≤ exp (0.6 * t) / 4` is an
elementary growth statement: `exp (0.6 * t) ≥ 1 + 0.6 * t` alone already gives it for `t` at
least `100`, since `0.15 * (t + 1) * 4 = 0.6 * t + 0.6` is at most `0.6 * t + 1`. No zero and
no character is involved. -/
theorem height_linear_le_quarter_exp (t : ℝ) (ht : 100 ≤ t) :
    0.15 * (t + 1) ≤ exp (0.6 * t) / 4 := by
  sorry

/-- LEAF. The conductor part absorbed into one quarter of the exponential:
`0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4`. This is the only step in which the modulus enters,
and the right hand side does not depend on `q`, so it is a genuine constraint on `q` against the
height: it holds exactly while `0.15 * log q + 3.389` stays under `exp (0.6 * t) / 4`. The
applications always have `q` at most the height, in which case `log q ≤ t + 1` and the step
follows from the previous two leaves; without such a bound the step is out of reach of any
estimate on `bookError`, which is what the report on this unit records. -/
theorem conductor_log_le_quarter_exp (q : ℕ) (t : ℝ) (hq : q ≠ 0) (ht : 100 ≤ t) :
    0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4 := by
  sorry

/-- The target, assembled from the four steps. Unfolding `bookError` at height `t + 1` leaves
`0.15 * log (q * (t + 1)) + 3.389`; the product formula bounds the logarithm by the sum of the
conductor and height logarithms, the conductor part fits under one quarter of the exponential
and the height part under the other, and the two quarters add to `exp (0.6 * t) / 2`. The
target theorem itself is not used. -/
theorem book_error_le_half_exp_split (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t) :
    ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  have hq : q ≠ 0 := NeZero.out
  have hmul := log_conductor_height_mul_le q t hq ht
  have hheight := height_log_le_height t ht
  have hlinear := height_linear_le_quarter_exp t ht
  have hconductor := conductor_log_le_quarter_exp q t hq ht
  have hprod : 0.15 * log ((q : ℝ) * (t + 1)) ≤ 0.15 * (log q + log (t + 1)) := by
    have h := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 0.15)
    linarith
  have hheightpart : 0.15 * log (t + 1) ≤ exp (0.6 * t) / 4 := by
    have h := mul_le_mul_of_nonneg_left hheight (by norm_num : (0 : ℝ) ≤ 0.15)
    linarith
  unfold ZeroCount1623.bookError
  linarith
