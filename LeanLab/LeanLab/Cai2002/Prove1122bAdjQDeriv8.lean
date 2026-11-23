/-
Split of the LEAF leafB8_adjQ_deriv of Split1122bAdjoint8.lean: the delay relation
s q'(s) = - q(s + 1) of the adjoint function q of the linear sieve, Nathanson Theorem 9.4,
as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf,
page 6. Here q(s) = the integral over x > 0 of exp (- s x - Ein x).
The twin leafB8_adjQ_deriv_twin, statement copied verbatim, is proved from two LEAFs:
differentiation under the integral sign, and an integration by parts identity.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjoint8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- LEAF: adjqderiv8 differentiation under the integral sign, Nathanson Theorem 9.4 as
quoted by BJS arXiv 2207.09452 page 6: for s > 0, q'(s) = - the integral over x > 0 of
x exp (- s x - Ein x). Domination on a neighbourhood [s/2, 3s/2] by x exp (- s x / 2),
using 0 ≤ Ein x for x ≥ 0, via hasDerivAt_integral_of_dominated_loc_of_deriv_le.
Class MEDIUM: dominated differentiation of a parameter integral on (0, ∞). -/
theorem leafB8_adjQ_hasDeriv_under (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8
      (-∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) s := by
  sorry

/-- LEAF: adjqderiv8 integration by parts, Nathanson Theorem 9.4 as quoted by BJS
arXiv 2207.09452 page 6: for s > 0, s times the integral over x > 0 of
x exp (- s x - Ein x) equals q(s + 1). Integrate d/dx (x exp (- s x - Ein x)) over (0, ∞);
the boundary terms vanish, and x Ein'(x) = 1 - e ^ -x turns the derivative into
exp (- s x - Ein x) - s x exp (- s x - Ein x) - (1 - e ^ -x) exp (- s x - Ein x).
Class MEDIUM: integration by parts on (0, ∞) with the fundamental theorem for Ein. -/
theorem leafB8_adjQ_ibp (s : ℝ) (hs : 0 < s) :
    s * ∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) = adjQB8 (s + 1) := by
  sorry

/-- Twin of leafB8_adjQ_deriv of Split1122bAdjoint8.lean, statement copied verbatim,
from the two LEAFs above. -/
theorem leafB8_adjQ_deriv_twin (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8 (-adjQB8 (s + 1) / s) s := by
  have h1 := leafB8_adjQ_hasDeriv_under s hs
  have h2 := leafB8_adjQ_ibp s hs
  have hI : (∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) = adjQB8 (s + 1) / s := by
    rw [← h2, mul_div_cancel_left₀ _ hs.ne']
  rw [hI] at h1
  convert h1 using 1
  ring

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_deriv_twin
