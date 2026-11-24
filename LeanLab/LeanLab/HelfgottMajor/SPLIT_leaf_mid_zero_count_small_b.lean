import LeanLab.HelfgottMajor.SPLIT_zero_count_mid_height
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Second split of `leaf_mid_zero_count_small` in `HelfgottMajor.SPLIT_zero_count_mid_height`.

Why a second split.  The first split, `SPLIT_leaf_mid_zero_count_small.lean`, reduces the
target to its leaf `leaf_mid_zero_count_at_exp`, the count at the fixed height `2 * π * exp 1`
for every primitive character of conductor at most `17`.  That leaf is numerically FALSE:
for `q = 17` and the character of order `16` sending the primitive root `3` to
`exp (2 * π * I / 16)`, the Hardy function of `L (s, χ)` changes sign `16` times on
`|t| ≤ 2 * π * exp 1`, so the count is at least `16 > 13`.  The first split lost the coupling
`q * t ≤ 2 * π * exp 1` between the height and the conductor.

This split keeps the coupling.  At the ranging height `t ≥ 1` the two sided closed count of
P0014, the book chapter 16 pages 431 and 432 with error display 16.21, as recorded in
`ZeroCount1623.zero_count_two_sided`, gives

  count ≤ (t / π) * log (q * t / (2 * π * exp 1)) + 0.3 * log (q * t) + 6.778.

On the middle range the logarithm of `q * t / (2 * π * exp 1)` is at most `0`, and
`log (q * t) ≤ log (2 * π) + 1 < 2.84`, so the right side is below `7.64 ≤ 13`.

The only open input is the shared LEAF `ZeroCount1623.book_zero_count`, the book display 3.95,
through `ZeroCount1623.zero_count_two_sided`.  So `leaf_mid_zero_count_small_split` below is
CONDITIONAL ON `book_zero_count` and has no sorry of its own.
AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The multiplicity weighted zero count below a height is the finite sum of the
multiplicities over the zeros in the strip below that height.  Same proof as the private
lemma of `SPLIT_zero_count_endpoint_short`. -/
private lemma zeroCount_eq_strip_sum_b (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) :
    zeroCount χ T = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  rw [zeroCount]
  simp only [zeroWeight, ZeroCount1623.mult]
  rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))]
  exact ZeroCount1623.tsum_zeroIdx χ T (fun z => (ZeroCount1623.mult χ z : ℝ))

/-- Arithmetic of the middle range: with `2 * π ≤ q * t ≤ 2 * π * exp 1` the right side of
the two sided closed count is at most `13`. -/
private lemma mid_closed_count_rhs_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t ≤ 13 := by
  have ht0 : 0 < t := by linarith
  have hqt0 : 0 < (q : ℝ) * t := lt_of_lt_of_le (by positivity) hlo
  have hmain : ZeroCount1623.bookMain q t ≤ 0 := by
    unfold ZeroCount1623.bookMain
    have hle1 : (q : ℝ) * t / (2 * π * exp 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr hhi
    have hlog : log ((q : ℝ) * t / (2 * π * exp 1)) ≤ 0 :=
      log_nonpos (div_pos hqt0 (by positivity)).le hle1
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht0.le (by positivity)) hlog
  have hlogqt : log ((q : ℝ) * t) ≤ log (2 * π) + 1 := by
    have h := log_le_log hqt0 hhi
    rwa [log_mul (by positivity) (exp_pos 1).ne', log_exp] at h
  have hl2pi : log (2 * π) ≤ 2 * π - 1 := log_le_sub_one_of_pos (by positivity)
  have hpi : π < 3.1416 := pi_lt_d4
  have herr : ZeroCount1623.bookError q t ≤ 0.15 * (2 * π) + 3.389 := by
    unfold ZeroCount1623.bookError
    linarith
  linarith

/-- The sealed statement, CONDITIONAL ON `ZeroCount1623.book_zero_count` through the two
sided closed count `ZeroCount1623.zero_count_two_sided` at the height `t ≥ 1`. -/
theorem leaf_mid_zero_count_small_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    zeroCount χ t ≤ 13 := by
  have h2 := ZeroCount1623.zero_count_two_sided χ hχ ht
  have h3 := mid_closed_count_rhs_le q t ht hlo hhi
  rw [zeroCount_eq_strip_sum_b q χ t]
  have h4 := (abs_le.mp h2).2
  linarith

end LeanLab.HelfgottMajor.Decomp388a
