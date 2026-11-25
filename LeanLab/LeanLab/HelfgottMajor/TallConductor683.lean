import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Elementary error budgets for the conductor above the height.
The error is Helfgott book chapter 16 page 431 display 16.21.
These are consequences of the error definition, with no zero count input.
The proposed argument budget in the beyond squared leaf comments is strictly
larger than the allowed error. This comparison does not refute the count bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.TallConductor683
open Real ZeroCount1623

/-- Page 431 display 16.21. For height at least one and conductor at most the
square of the height, the error is at most 0.45 log T plus 3.389. -/
theorem bookError_le_height_budget (q : ℕ) [NeZero q] {T : ℝ}
    (hT : 1 ≤ T) (hqs : (q : ℝ) ≤ T ^ 2) :
    bookError q T ≤ 0.45 * log T + 3.389 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hTp : 0 < T := by linarith
  have hlog : log (q : ℝ) ≤ 2 * log T := by
    have h := Real.log_le_log hqp hqs
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  unfold bookError
  rw [Real.log_mul hqp.ne' hTp.ne']
  linarith

/-- Page 431 display 16.21. Beyond the squared conductor cut, the error is
at most 0.225 log q plus 3.389. -/
theorem bookError_le_conductor_budget (q : ℕ) [NeZero q] {T : ℝ}
    (hT : 1 ≤ T) (hqs : T ^ 2 ≤ (q : ℝ)) :
    bookError q T ≤ 0.225 * log (q : ℝ) + 3.389 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hTp : 0 < T := by linarith
  have hlog : 2 * log T ≤ log (q : ℝ) := by
    have h := Real.log_le_log (sq_pos_of_pos hTp) hqs
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  unfold bookError
  rw [Real.log_mul hqp.ne' hTp.ne']
  linarith

/-- Beyond the squared conductor cut, the proposed 0.23 log q plus 3.4 argument
budget is strictly larger than the error allowed by page 431 display 16.21. -/
theorem bookError_lt_argument_budget (q : ℕ) [NeZero q] {T : ℝ}
    (hT : 1 ≤ T) (hqs : T ^ 2 ≤ (q : ℝ)) :
    bookError q T < 0.23 * log (q : ℝ) + 3.4 := by
  have hbudget := bookError_le_conductor_budget q hT hqs
  have hlog := Real.log_natCast_nonneg q
  linarith

/-- Even half of the older two sided error from arXiv page 38 display 4.26
is strictly larger than the error in book page 431 display 16.21. -/
theorem bookError_lt_half_arxiv_error (q : ℕ) [NeZero q] {T : ℝ}
    (hT : 1 ≤ T) :
    bookError q T < (0.5 * log ((q : ℝ) * T) + 17.7) / 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hprod : 1 ≤ (q : ℝ) * T := by nlinarith
  have hlog := Real.log_nonneg hprod
  unfold bookError
  linarith

end LeanLab.HelfgottMajor.TallConductor683
