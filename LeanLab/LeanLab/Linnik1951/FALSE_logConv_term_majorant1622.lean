/-
FALSIFY unit Linnik1951/SPLIT_logConv_excess1622.
The sealed leaf logConv_term_majorant1622 of SPLIT_logConv_excess1622.lean is false as
stated. Its hypotheses bound only the sum u + v, so one factor may be tiny while the
other is close to 2 L. The witness is u = 1/100, v = 199/100, L = 1: the sum is 2 L,
the shift is 0, the right side is 1 and the left side is 10000/199, about 50.25.
This audits the split annotation only. The estimate of the paper, page 161 after
equation 6.3, has u = log m and v = log (n - m), both at most L = log n, and with
those two bounds the estimate holds: see logConv_term_majorant_bounded474.
This file is standalone and does not import the file holding the open leaf, so its
theorems cannot depend on that sorry. No definition is added and no statement of
any other file is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace LeanLab.Linnik1951

/-- Explicit counterexample to the sealed leaf logConv_term_majorant1622: the point
u = 1/100, v = 199/100, L = 1 meets every hypothesis of that leaf, with u + v = 2 L
and shift 0, and the conclusion fails there, since 1 / (u v) = 10000/199 exceeds 1. -/
theorem logConv_term_majorant1622_counterexample :
    ∃ u v L : ℝ, 0 < u ∧ 0 < v ∧ 0 < L ∧ u + v ≤ 2 * L ∧ 2 * L - (u + v) ≤ L / 2 ∧
      1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v)) < 1 / (u * v) := by
  refine ⟨1 / 100, 199 / 100, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The statement of the sealed leaf logConv_term_majorant1622, quantified over all
real u, v, L exactly as in SPLIT_logConv_excess1622.lean, is false. -/
theorem logConv_term_majorant1622_false :
    ¬ (∀ (u v L : ℝ), 0 < u → 0 < v → 0 < L →
      u + v ≤ 2 * L → 2 * L - (u + v) ≤ L / 2 →
      1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v))) := by
  intro h
  obtain ⟨u, v, L, hu, hv, hL, hsum, hshift, hlt⟩ := logConv_term_majorant1622_counterexample
  exact absurd (h u v L hu hv hL hsum hshift) (not_le.mpr hlt)

end LeanLab.Linnik1951
