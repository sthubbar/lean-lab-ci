/-
Split of the LEAF leafB8_adjoint of Split1122bBoundary8.lean: the adjoint function of the
linear sieve, Nathanson Theorem 9.4, as quoted by Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, page 6. The adjoint function is
q(s) = the integral over x > 0 of exp (- s x - Ein x), with
Ein x = the integral over [0, x] of (1 - e ^ -t) / t. It satisfies s q'(s) = - q(s + 1)
for s > 0, s q(s) → 1 as s → ∞, and K(q) = e ^ -γ. Numerically K(q) = 0.5614595.
The twin leafB8_adjoint_twin, statement copied verbatim, is proved from three LEAFs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The entire exponential integral Ein x = the integral over [0, x] of (1 - e ^ -t) / t,
used in the adjoint function of Nathanson Theorem 9.4, as quoted by BJS arXiv 2207.09452
page 6. -/
def einB8 (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t

/-- The adjoint function of Nathanson Theorem 9.4, as quoted by BJS arXiv 2207.09452 page 6:
q(s) = the integral over x > 0 of exp (- s x - Ein x). -/
def adjQB8 (s : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), exp (-s * x - einB8 x)

/-- LEAF: Nathanson Theorem 9.4, the delay relation of the adjoint function: for s > 0,
q'(s) = - the integral of x exp (- s x - Ein x) by differentiation under the integral, and
integrating by parts with d/dx exp (- s x - Ein x) = - (s + (1 - e ^ -x) / x) times the
integrand gives s q'(s) = - q(s + 1). Class MEDIUM: dominated differentiation of a
parameter integral plus integration by parts on (0, ∞). -/
theorem leafB8_adjQ_deriv (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8 (-adjQB8 (s + 1) / s) s := by
  sorry

/-- LEAF: Nathanson Theorem 9.4, normalization of the adjoint function: s q(s) → 1 as
s → ∞, by the substitution x = y / s, s q(s) = the integral over y > 0 of
exp (- y - Ein (y / s)), and Ein (y / s) → 0 with 0 ≤ Ein, dominated convergence. Class
MEDIUM: dominated convergence on (0, ∞) and continuity of Ein at 0. -/
theorem leafB8_adjQ_tendsto :
    Filter.Tendsto (fun s => s * adjQB8 s) Filter.atTop (nhds 1) := by
  sorry

/-- LEAF: Nathanson Theorem 9.4, the Mertens type constant: for the explicit adjoint
function, K(q) = q(3) (1 + log 2) + the integral over [2, 3] of
(1 + log (t - 1)) q(t + 1) / t equals e ^ -γ, through Ein x = log x + γ + E_1(x) and the
integral of e ^ -t / t. Numerically K(q) = 0.5614595. Class HARD: Laplace transform
identities and γ as a limit of the exponential integral. -/
theorem leafB8_adjQ_K : kConstB8 adjQB8 = exp (-eulerMascheroniConstant) := by
  sorry

/-- Twin of leafB8_adjoint of Split1122bBoundary8.lean, statement copied verbatim, from
the three LEAFs above with q the explicit adjoint function adjQB8. -/
theorem leafB8_adjoint_twin :
    ∃ q : ℝ → ℝ, IsAdjB8 q ∧ kConstB8 q = exp (-eulerMascheroniConstant) :=
  ⟨adjQB8, ⟨fun s hs => leafB8_adjQ_deriv s hs, leafB8_adjQ_tendsto⟩, leafB8_adjQ_K⟩

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjoint_twin
