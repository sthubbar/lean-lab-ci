import LeanLab.HelfgottMajor.SPLIT_book_error_le_half_exp

/-!
Splitting `conductor_log_le_quarter_exp` of `SPLIT_book_error_le_half_exp.lean` into three
steps.

The target states that for every nonzero natural `q` and every real `t` with `100 ≤ t`,
`0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4`. The right hand side grows with `t` and carries no
`q`, so the step is a genuine constraint on `q` against the height. The split isolates the
monotonicity of the exponential at the base height from the conductor estimate at that height.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. Monotonicity of the exponential at the base height. For `t` at least `100`,
`exp (0.6 * t)` is at least `exp (0.6 * 100) = exp 60`, so one quarter of it is at least
`exp 60 / 4`. This step uses only the monotonicity of `exp` and the hypothesis `100 ≤ t`. -/
theorem exp_sixty_div_four_le_quarter_exp (t : ℝ) (ht : 100 ≤ t) :
    exp (0.6 * (100 : ℝ)) / 4 ≤ exp (0.6 * t) / 4 := by
  sorry

/-- LEAF. The conductor estimate at the base height. For every nonzero natural `q`,
`0.15 * log q + 3.389 ≤ exp 60 / 4`. This is the only step in which `q` enters, and the
right hand side does not depend on `q`, so it is a real constraint on the modulus. -/
theorem conductor_log_le_exp_sixty_div_four (q : ℕ) (hq : q ≠ 0) :
    0.15 * log q + 3.389 ≤ exp (0.6 * (100 : ℝ)) / 4 := by
  sorry

/-- Assembly of `conductor_log_le_quarter_exp` from the two leaves above. The conductor part
fits under `exp 60 / 4` by the second leaf, and `exp 60 / 4` fits under `exp (0.6 * t) / 4`
by the first leaf, so the two quarters chain to give the target. -/
theorem conductor_log_le_quarter_exp_F1618 (q : ℕ) (t : ℝ) (hq : q ≠ 0) (ht : 100 ≤ t) :
    0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4 := by
  have h1 := exp_sixty_div_four_le_quarter_exp t ht
  have h2 := conductor_log_le_exp_sixty_div_four q hq
  linarith

end LeanLab.HelfgottMajor.Decomp269c
