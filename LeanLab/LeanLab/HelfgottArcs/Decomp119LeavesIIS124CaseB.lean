/-
P0013 page 72, case b of the Type II bound, split once into two cited leaves:
the display obtained from 5.36, and the maximum of its ratio to x^{5/6} (log x)^{3/2}.
The constants κ2, κ6, κ7, κ9 enter through the paper's stated upper bounds
κ2 ≤ 1.93768 on page 57, κ6 = 0.60428 on page 58, κ7 ≤ 0.1281 on page 59 and κ9 ≤ 3.9086 on page 56;
every term of the display is monotone in them.
A float check of the display gives the ratio 0.2495513 at x = 2.16e20, decreasing in x.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesII

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB
open LeanLab.HelfgottArcs.Decomp119

/-- P0013 page 68 display 5.55: the function ̥(q) = e^γ log log q + 2.50637/log log q,
with q/φ(q) < ̥(q) by Rosser and Schoenfeld 1962 Theorem 15. -/
noncomputable def frakF (t : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) +
    2.50637 / Real.log (Real.log t)

/-- P0013 page 72, the display for case b obtained from 5.36 with θ = e^2, q ≤ y,
8y < |δ|q ≤ U, written with y = x^{1/3}/6, Q = x/U and the bounds for κ2, κ6, κ7, κ9. -/
noncomputable def caseBDisplay (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  2 * x * Real.sqrt (frakF y) / Real.sqrt (8 * y) *
      Real.sqrt ((Real.log (x / (U x * Real.exp 2 * (8 * y))) +
          Real.log (3 * y) * Real.log (Real.log (x / (3 * U x * y)) /
            Real.log (8 * Real.exp 2 / 3))) *
        (κ6 * Real.log (x / (U x * Real.exp 2 * (2 * y))) + 2 * κ7)) +
    2 * κ2 / 3 * (x / Real.sqrt (16 * y) *
        (Real.log (8 * Real.exp 2 * y) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2)) +
      x / 4 / Real.sqrt (Q - y) *
        (Real.log (Real.exp 2 * U x) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2))) +
    (κ2 / Real.sqrt (2 * (1 - y / Q)) *
        (Real.sqrt (Real.log (V x)) + Real.sqrt (1 / Real.log (V x))) + κ9) *
      (x / Real.sqrt (V x)) +
    κ2 * Real.sqrt (2 * frakF y) *
      Real.sqrt (Real.log (Real.exp 2 * U x) / Real.log (8 * Real.exp 2 / 3)) *
      (x / Real.sqrt (U x))

/-- LEAF: P0013 page 72, case b: from 5.36 on page 62, with q/φ(q) ≤ ̥(y), |δ| > 8,
8y < |δq| ≤ x/Q = U and q ≤ y, |S_II| is at most the displayed expression. Class HARD. -/
theorem caseB_display536 (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hb1 : 8 < |δ'|) (hb2 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')
    (hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    ‖II α x‖ ≤ caseBDisplay x := by
  sorry

/-- LEAF: P0013 page 72, "We take the maximum of the ratio of this to x^{5/6}(log x)^{3/2}":
the case b display is at most 0.24956 x^{5/6} (log x)^{3/2} for x ≥ 2.16e20.
Class MEDIUM, a numerical bound; float value 0.2495513 at x = 2.16e20. -/
theorem caseB_ratio (x : ℝ) (hx : 2.16e20 ≤ x) :
    caseBDisplay x ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- Assembly of Decomp119LeavesII.caseB from the two leaves, exact parent statement. -/
theorem caseB_of_leaves (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hb1 : 8 < |δ'|) (hb2 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')
    (hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    ‖II α x‖ ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) :=
  le_trans (caseB_display536 x α hx a' q' δ' h2α hg hq1 hδ hb1 hb2 hy) (caseB_ratio x hx)

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB
