/-
The one open leaf under `major_minor_mean_square150` of Decomp150a.lean, P0029 pages 11 and 12.

REPAIR 20261112: the gate rejected claude/BhowmikGrimmelt2026-theorem31_inputs150-p3 because this
leaf sat in the existing file Decomp150a.lean and raised its sorry count.  The leaf is moved here
verbatim, statement unchanged, and Decomp150a.lean imports this file and proves
`major_minor_mean_square150` from it.  CITED-LEFT: the survey proves this step only by citing
Hardy and Littlewood 1923, so it is not split further.

Binary Goldbach is OPEN.  AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 pages 11 and 12, display 3.5 with the Gauss sum bound 3.6 and the zero bound 3.7.
Under `ZeroBound Θ`, on every Dirichlet arc of denominator `q ≤ Q ≍ X^{1/2}` the prime sum differs
from its main term `μ(q)/φ(q) T(α - a/q)` by `≪ q^{1/2} X^{Θ + ε} ≪ X^{Θ + 1/4 + ε}`.  The survey
states 3.7 at the arc centres with weight `e^{-n/N}`; the sharp cutoff, arc uniform form
`X^{Θ+ε} (q (1 + |β| X))^{1/2}`, `|β| ≤ 1/(qQ)`, is the Hardy and Littlewood 1923 input it cites.  CITED-LEFT, OPEN: needs the explicit formula
for `ψ(x, χ)` uniformly in `q`, not in Mathlib. -/
theorem major_arc_uniform150 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  sorry

end LeanLab.BhowmikGrimmelt2026
