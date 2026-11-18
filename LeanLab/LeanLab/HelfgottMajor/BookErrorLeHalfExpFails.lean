import LeanLab.HelfgottMajor.ZeroCount1623

/-!
`book_error_le_half_exp` of `SPLIT_zero_multiplicity_subexponential.lean` is FALSE as stated.

That statement reads: for every natural `q` with `NeZero q` and every real `t` with `100 ≤ t`,
`ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2`.
By definition `bookError q T = 0.15 * log (q * T) + 3.389`. The left side grows without bound
in the modulus `q` at a fixed height, while the right side does not depend on `q`. So the
statement fails at every fixed height once `q` is large enough.

The witness at height `t` is `q = ⌈exp (10 * exp (0.6 * t))⌉₊`. Then
`log (q * (t + 1)) ≥ log q ≥ 10 * exp (0.6 * t)`, so
`bookError q (t + 1) ≥ 1.5 * exp (0.6 * t) + 3.389`, which exceeds `exp (0.6 * t) / 2`.

This file imports only `ZeroCount1623`, where `bookError` is defined, so none of its theorems
can depend on an open leaf. The statement refuted below is copied word for word from the leaf.
No statement on main is changed. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real

/-- At every height `t ≥ 0` there is a nonzero modulus `q` for which the explicit error
`bookError q (t + 1) = 0.15 * log (q * (t + 1)) + 3.389` is strictly larger than
`exp (0.6 * t) / 2`. The modulus is `⌈exp (10 * exp (0.6 * t))⌉₊`. This is standard: the
logarithm is unbounded in `q` and the right hand side carries no `q`. -/
theorem book_error_gt_half_exp_of_large_conductor (t : ℝ) (ht : 0 ≤ t) :
    ∃ q : ℕ, q ≠ 0 ∧ exp (0.6 * t) / 2 < ZeroCount1623.bookError q (t + 1) := by
  have hE : 0 < exp (0.6 * t) := exp_pos _
  have hpos : 0 < exp (10 * exp (0.6 * t)) := exp_pos _
  refine ⟨⌈exp (10 * exp (0.6 * t))⌉₊, (Nat.ceil_pos.mpr hpos).ne', ?_⟩
  have hq : exp (10 * exp (0.6 * t)) ≤ ((⌈exp (10 * exp (0.6 * t))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hprod : exp (10 * exp (0.6 * t)) ≤
      ((⌈exp (10 * exp (0.6 * t))⌉₊ : ℕ) : ℝ) * (t + 1) := by
    nlinarith
  have hlog : 10 * exp (0.6 * t) ≤
      log (((⌈exp (10 * exp (0.6 * t))⌉₊ : ℕ) : ℝ) * (t + 1)) := by
    calc 10 * exp (0.6 * t) = log (exp (10 * exp (0.6 * t))) := (log_exp _).symm
      _ ≤ _ := log_le_log hpos hprod
  unfold ZeroCount1623.bookError
  linarith

/-- The leaf `book_error_le_half_exp` is false as stated. The quantified statement is the leaf's
statement word for word; it fails at height `t = 100` for the modulus given by
`book_error_gt_half_exp_of_large_conductor`. -/
theorem book_error_le_half_exp_false :
    ¬ ∀ (q : ℕ) [NeZero q] (t : ℝ), 100 ≤ t →
      ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  intro h
  obtain ⟨q, hq0, hlt⟩ := book_error_gt_half_exp_of_large_conductor 100 (by norm_num)
  have : NeZero q := ⟨hq0⟩
  exact absurd (h q 100 le_rfl) (not_le.mpr hlt)

/-- The same failure at every admissible height: for each `t ≥ 100` the leaf's inequality fails
for some nonzero modulus. So no restriction of the height alone repairs the leaf; a repair has
to bound `q` against the height. -/
theorem book_error_le_half_exp_false_at_every_height (t : ℝ) (ht : 100 ≤ t) :
    ¬ ∀ (q : ℕ) [NeZero q], ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  intro h
  obtain ⟨q, hq0, hlt⟩ := book_error_gt_half_exp_of_large_conductor t (by linarith)
  have : NeZero q := ⟨hq0⟩
  exact absurd (h q) (not_le.mpr hlt)

end LeanLab.HelfgottMajor.Decomp269c
