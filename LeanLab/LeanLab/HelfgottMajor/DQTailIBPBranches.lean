import LeanLab.HelfgottMajor.TailIntegral123
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Split of `DQTailCountSplit.stieltjes_integral_le_tail` by envelope branch, burst-20261124 S1,
tag dq_ibp_split. P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4,
page 41 display 4.36 for the exponential branch and page 42 displays 4.37 to 4.41 for the
Gaussian branch. Each LEAF is the integration by parts for one branch of the envelope of
display 3.4 on page 10, with the boundary term that page 38 drops, and also asserts the
integrability needed to add the two branches. No new definitions.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DQTailIBPBranches
open Real LeanLab.HelfgottMajor MeasureTheory

/-- LEAF: P0014 page 41, display 4.36, exponential branch f of t = e to the minus 0.1598 t.
Class MEDIUM, pure real analysis. Integration by parts on Ioi T against g of t =
2 bookMain t - 2 bookMain T + 2 bookError t - 2 bookError T, g of T = 0, g prime at most
2 countDensity, plus the constant 4 bookError T which gives 4 f of T bookError T. -/
theorem exp_branch_ibp (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    IntegrableOn (fun t => 0.1598 * exp (-0.1598 * t) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T)) (Set.Ioi T) ∧
    (∫ t in Set.Ioi T, 0.1598 * exp (-0.1598 * t) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T)) ≤
      2 * TailIntegral123.expTailIntegral q T +
        4 * exp (-0.1598 * |T|) * ZeroCount1623.bookError q T := by
  sorry

/-- LEAF: P0014 page 42, displays 4.37 to 4.41, Gaussian branch f of t =
e to the minus 0.1065 times t over pi delta squared, delta nonzero. Class MEDIUM.
Same integration by parts as `exp_branch_ibp`, minus f prime being
0.213 t over pi delta squared times f, since 2 times 0.1065 is 0.213. -/
theorem gaussian_branch_ibp (q : ℕ) [NeZero q] (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    IntegrableOn (fun t => 0.213 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T)) (Set.Ioi T) ∧
    (∫ t in Set.Ioi T,
        0.213 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T)) ≤
      2 * TailIntegral123.gaussianTailIntegral q δ T +
        4 * exp (-0.1065 * (|T| / (π * |δ|)) ^ 2) * ZeroCount1623.bookError q T := by
  sorry

end LeanLab.HelfgottMajor.DQTailIBPBranches
