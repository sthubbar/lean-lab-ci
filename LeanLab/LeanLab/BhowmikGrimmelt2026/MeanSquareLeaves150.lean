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
import LeanLab.BhowmikGrimmelt2026.Decomp502a

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 pages 11 and 12, display 3.5 with the Gauss sum bound 3.6 and the zero bound 3.7.
Under `ZeroBound Θ`, at the arc centres the smoothed prime sum differs from its main term
by `≪ q^{1/2} X^{Θ + ε} ≪ X^{Θ + 1/4 + ε}`, the right hand side of 3.7.
The theorem below requires a sharp sum throughout every assigned arc.  The survey states 3.7 only at the centres of the arcs and for the
smoothed power series `f(e(a/q) e^{-1/N})`, not for the sharp sum `S`.  The bound uniform over
the arc, in the sharp form `X^{Θ+ε} (q (1 + |β| X))^{1/2}` with `|β| ≤ 1/(qQ)`, is not stated in
the survey: it is the standard consequence of the truncated explicit formula for `ψ(x, χ)` under
`ZeroBound Θ`.  The survey's reference for Theorem 3.1 is its [10], Hardy and Littlewood 1923,
Partitio Numerorum III, Acta Math. 44.  Architect pass U-1662 checked it numerically at
`X = 400, 1600, 3600`, max `|S - V| / X^{3/4}` about 0.5 to 0.65.
OPEN: psi_zero_expansion504 supplies the uniform sharp character formula as a leaf.
major_arc_partial_summation504 retains the oscillatory zero mode estimate and assembly. -/
theorem major_arc_uniform150 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := major_arc_partial_summation504 Θ hΘ hZ
    (psi_zero_expansion504 Θ hΘ hZ) ε hε
  refine ⟨max 1 C, fun X hX α hα => ?_⟩
  by_cases hX2 : 2 ≤ X
  · exact (hC X hX2 α hα).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (by positivity))
  · have hX1 : X = 1 := by omega
    subst X
    rw [major_error_one504]
    simpa using le_max_left (1 : ℝ) C

/-- LEAF: P0029 page 12, the arc tails pointwise.  `V² - W` is minus the sum over
`q ≤ Q = ⌊X^{1/2}⌋`, `(a, q) = 1`, of `μ(q)²/φ(q)² T(α - a/q)²` over the fractions `a/q` whose
arc does not contain `α`, with `|T(β)| ≤ min(X, 1/(2‖β‖))`.  The claim is
`|V(α)² - W(α)| ≪ X^{1+ε}` uniformly: the fractions within `1/(qQ)` of `α` but not assigned to
it have `q ≥ Q/2`, by the least denominator condition together with Farey spacing
`|a/q - a'/q'| ≥ 1/(q q')`, and there are `O(1)` of them,
each `≤ X²/φ(q)² ≪ X^{1+ε}`; the others give `Σ_{q ≤ Q} φ(q)^{-2} min(X², q²/‖qα‖²) ≪ X^{1+ε}`
by the standard count of `q` with `‖qα‖` small.  This is the `O(N^{1/2+ε})` of page 12, which
the survey states without proof. PROVED by the assigned residue cancellation in near_arc_tail502
and the dyadic inverse square estimate in far_kernel502. -/
theorem arc_tails_sup150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  -- Both near and far estimates have clean proofs in Decomp502a and Decomp504a.
  exact arc_tails_of_near_far502 near_arc_tail502 far_arc_tail502

end LeanLab.BhowmikGrimmelt2026
