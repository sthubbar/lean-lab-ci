import Mathlib

/-!
Disproof of the leaf `conductor_log_le_quarter_exp` of
`LeanLab/HelfgottMajor/SPLIT_book_error_le_half_exp.lean`.

That leaf states, for every nonzero natural `q` and every real `t` with `100 ≤ t`,
`0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4`. The right hand side does not depend on `q`, and
nothing bounds `q`, so the statement is false: at `t = 100` the right side is the fixed number
`exp 60 / 4`, while `q = ⌈exp (4 * exp 60)⌉₊` has `log q ≥ 4 * exp 60`, so the left side is at
least `0.6 * exp 60 + 3.389`, which exceeds `exp 60 / 4`.

The same counterexample refutes the parent statement `book_error_le_half_exp` shape, since
`bookError q (t + 1) = 0.15 * log (q * (t + 1)) + 3.389` also grows without bound in `q`; that
second fact is recorded here for the explicit formula only, with no reference to `bookError`.

This file states the negation of the exact hypothesis list and inequality of the leaf, with the
same numerals, and imports only Mathlib, so it does not depend on the `sorry` it refutes.
AI wrote this Lean code.
-/

namespace LeanLab.HelfgottMajor.FalseConductorLog
open Real

/-- The witness modulus `⌈exp (4 * exp 60)⌉₊` is nonzero and its logarithm is at least
`4 * exp 60`. Standard: `x ≤ ⌈x⌉₊` and monotonicity of the logarithm. -/
theorem witness_log_ge :
    (⌈exp (4 * exp 60)⌉₊ ≠ 0) ∧ 4 * exp 60 ≤ log (⌈exp (4 * exp 60)⌉₊ : ℝ) := by
  have h1 : exp (4 * exp 60) ≤ (⌈exp (4 * exp 60)⌉₊ : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < (⌈exp (4 * exp 60)⌉₊ : ℝ) := lt_of_lt_of_le (exp_pos _) h1
  refine ⟨?_, ?_⟩
  · intro h0
    rw [h0] at hpos
    simp at hpos
  · have h := Real.log_le_log (exp_pos _) h1
    rwa [Real.log_exp] at h

/-- The explicit counterexample: at `q = ⌈exp (4 * exp 60)⌉₊` and `t = 100` the inequality of
`conductor_log_le_quarter_exp` fails strictly. -/
theorem conductor_log_gt_quarter_exp_at_witness :
    exp (0.6 * (100 : ℝ)) / 4 < 0.15 * log (⌈exp (4 * exp 60)⌉₊ : ℝ) + 3.389 := by
  have hlog := witness_log_ge.2
  have e : (0.6 : ℝ) * 100 = 60 := by norm_num
  rw [e]
  have hexp := exp_pos (60 : ℝ)
  linarith

/-- FALSE. The negation of the leaf `conductor_log_le_quarter_exp`, with its exact binders,
hypotheses and inequality: it is not true that every nonzero natural `q` and every real `t`
with `100 ≤ t` satisfy `0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4`. -/
theorem conductor_log_le_quarter_exp_false :
    ¬ ∀ (q : ℕ) (t : ℝ), q ≠ 0 → 100 ≤ t → 0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4 := by
  intro h
  have hw := h ⌈exp (4 * exp 60)⌉₊ 100 witness_log_ge.1 le_rfl
  have hgt := conductor_log_gt_quarter_exp_at_witness
  linarith

/-- The same failure for the unsplit explicit formula `0.15 * log (q * (t + 1)) + 3.389`, the
value of `bookError q (t + 1)` as quoted in the split file's header: it is not bounded by
`exp (0.6 * t) / 2` for all nonzero `q` at `t = 100`. So the parent target has the same defect
and the repair is a re-cut with a bound on `q`, not a sharper estimate. -/
theorem explicit_book_error_le_half_exp_false :
    ¬ ∀ (q : ℕ) (t : ℝ), q ≠ 0 → 100 ≤ t →
      0.15 * log ((q : ℝ) * (t + 1)) + 3.389 ≤ exp (0.6 * t) / 2 := by
  intro h
  obtain ⟨hq0, hlog⟩ := witness_log_ge
  have hw := h ⌈exp (4 * exp 60)⌉₊ 100 hq0 le_rfl
  have h1 : exp (4 * exp 60) ≤ (⌈exp (4 * exp 60)⌉₊ : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < (⌈exp (4 * exp 60)⌉₊ : ℝ) := lt_of_lt_of_le (exp_pos _) h1
  have hmono : log (⌈exp (4 * exp 60)⌉₊ : ℝ)
      ≤ log ((⌈exp (4 * exp 60)⌉₊ : ℝ) * ((100 : ℝ) + 1)) :=
    Real.log_le_log hpos (by nlinarith)
  have e : (0.6 : ℝ) * 100 = 60 := by norm_num
  rw [e] at hw
  have hexp := exp_pos (60 : ℝ)
  have hchain : 4 * exp 60 ≤ log ((⌈exp (4 * exp 60)⌉₊ : ℝ) * ((100 : ℝ) + 1)) :=
    le_trans hlog hmono
  generalize log ((⌈exp (4 * exp 60)⌉₊ : ℝ) * ((100 : ℝ) + 1)) = X at hw hchain
  linarith

end LeanLab.HelfgottMajor.FalseConductorLog

#print axioms LeanLab.HelfgottMajor.FalseConductorLog.witness_log_ge
#print axioms LeanLab.HelfgottMajor.FalseConductorLog.conductor_log_gt_quarter_exp_at_witness
#print axioms LeanLab.HelfgottMajor.FalseConductorLog.conductor_log_le_quarter_exp_false
#print axioms LeanLab.HelfgottMajor.FalseConductorLog.explicit_book_error_le_half_exp_false
