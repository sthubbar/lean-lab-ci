/-
Split of the MEDIUM leaf caseB_ratio of Decomp119LeavesIIS124CaseB at x = 1e25.
An mpmath check at 30 digits: the four terms of the display, divided by x^{5/6} (log x)^{3/2},
are 0.135442, 0.061149, 0.051290, 0.001670 at x0 = 2.16e20, total 0.2495513.
Term 1 rises to about 0.17553 near 1e40, so the sum of the per-term suprema is 0.28964,
above 0.24956, and a per-term split would be false. Instead the range is cut at X1 = 1e25:
on [x0, X1] the maximum on a grid of 2001 points is 0.2495513, at x0, margin 8.7e-6;
on [X1, 1e325] the maximum on a grid of 6001 points is 0.2455632, at X1, margin 4.0e-3.
These are float grid checks, not proofs. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBRatio
open LeanLab.HelfgottArcs.Decomp119 LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB

/-- LEAF: P0013 page 72, the maximum of the case b ratio on the bounded range 2.16e20 ≤ x ≤ 1e25.
Class MEDIUM, a numerical bound; float maximum 0.2495513 at x = 2.16e20, margin 8.7e-6. -/
theorem caseB_ratio_low (x : ℝ) (hx : 2.16e20 ≤ x) (hx1 : x ≤ 1e25) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: P0013 page 72, the case b ratio on the unbounded range x ≥ 1e25.
Class MEDIUM, a numerical and asymptotic bound; float maximum 0.2455632 at x = 1e25, margin 4.0e-3;
term 1 peaks near 0.1755 at about 1e40 and every term ratio tends to 0. -/
theorem caseB_ratio_high (x : ℝ) (hx1 : 1e25 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- Assembly of caseB_ratio from the two leaves by cases on x ≤ 1e25, exact parent statement. -/
theorem caseB_ratio (x : ℝ) (hx : 2.16e20 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  rcases le_or_gt x 1e25 with h | h
  · exact caseB_ratio_low x hx h
  · exact caseB_ratio_high x h.le

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBRatio
