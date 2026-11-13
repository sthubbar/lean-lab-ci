/-
ROUTE BURST 7, 20261112, repair pass. The two open leaves of the split of
`major_minor_mean_square150` in `Decomp150a.lean`, moved out of that file into this new one: an
existing file may never gain a `sorry`, a new file carrying leaves may.  Nothing else lives here,
and every proof in `Decomp150a.lean` that used these two names still uses them, now through the
import of this module.

Both leaves are P0029, G. Bhowmik and L. Grimmelt 2026, "The exceptional set of the Goldbach
problem", arXiv 2607.27282 v2, Section 3, pages 11 and 12: the major arc expansion 3.5 with the
Gauss sum bound 3.6 and the zero bound 3.7, and the pointwise size of the arc tails of page 12.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150
import LeanLab.BhowmikGrimmelt2026.Coefficients150

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 pages 11 and 12, display 3.5 with the Gauss sum bound 3.6 and the zero bound 3.7.
Under `ZeroBound Θ`, on every Dirichlet arc of denominator `q ≤ Q ≍ X^{1/2}` the prime sum
differs from its main term `μ(q)/φ(q) T(α - a/q)` by `≪ q^{1/2} X^{Θ + ε} ≪ X^{Θ + 1/4 + ε}`,
the right hand side of 3.7.  The survey states 3.7 at the centres of the arcs; the bound uniform
over the arc, in the sharp form `X^{Θ+ε} (q (1 + |β| X))^{1/2}` with `|β| ≤ 1/(qQ)`, is the
Hardy and Littlewood 1923 Partitio Numerorum V input that the survey cites for Theorem 3.1.
OPEN: needs the explicit formula for `ψ(x, χ)` uniformly in `q`, not in Mathlib. -/
theorem major_arc_uniform150 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  sorry

/-- LEAF: P0029 page 12, the arc tails pointwise.  `V² - W` is minus the sum over
`q ≤ Q = ⌊X^{1/2}⌋`, `(a, q) = 1`, of `μ(q)²/φ(q)² T(α - a/q)²` over the fractions `a/q` whose
arc does not contain `α`, with `|T(β)| ≤ min(X, 1/(2‖β‖))`.  The claim is
`|V(α)² - W(α)| ≪ X^{1+ε}` uniformly: the fractions within `1/(qQ)` of `α` but not assigned to
it have `q > Q/2`, by the Farey spacing `|a/q - a'/q'| ≥ 1/(q q')`, and there are `O(1)` of them,
each `≤ X²/φ(q)² ≪ X^{1+ε}`; the others give `Σ_{q ≤ Q} φ(q)^{-2} min(X², q²/‖qα‖²) ≪ X^{1+ε}`
by the standard count of `q` with `‖qα‖` small.  This is the `O(N^{1/2+ε})` of page 12, which
the survey states without proof.  OPEN: the Farey counting is not in the lab. -/
theorem arc_tails_sup150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  sorry

end LeanLab.BhowmikGrimmelt2026
