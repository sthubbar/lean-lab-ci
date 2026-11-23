/-
Split of the LEAF leafB8_adjQ_K of Split1122bAdjoint8.lean: K(q) = e ^ -γ for the explicit
adjoint function q of Nathanson Theorem 9.4, as quoted by Bordignon, Johnston and
Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6.
Argument: with p(t) = 0 on (0, 1), p(t) = 1 / t on [1, 2], p(t) = (1 + log (t - 1)) / t on
[2, 3], one has (s p(s))' = p(s - 1), so the adjoint pairing s p(s) q(s) plus the integral
of p(t) q(t + 1) over [s - 1, s] is constant on [1, 3]; at s = 3 it is K(q), at s = 1 it is
q(1). Then d/dx (x e ^ -Ein x) = e ^ (-x - Ein x), so q(1) is the limit of X e ^ -Ein X,
which is e ^ -γ since Ein X = log X + γ + o(1).
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjoint8

open Real Filter Topology

noncomputable section

namespace LeanLab.Cai2002

/-- LEAF: Nathanson Theorem 9.4, adjoint pairing evaluated at s = 3 and s = 1: with
p(t) = 0 on (0, 1), 1 / t on [1, 2] and (1 + log (t - 1)) / t on [2, 3], s p(s) is
continuous at 2 and satisfies (s p(s))' = p(s - 1) on (1, 3), so by leafB8_adjQ_deriv
s q'(s) = - q(s + 1) the pairing s p(s) q(s) + the integral of p(t) q(t + 1) over
[s - 1, s] has zero derivative on (1, 2) and (2, 3); its value at 3 is kConstB8 q and its
limit at 1 from the right is q(1). Class MEDIUM: FTC for parameter integrals and
continuity of q on [1, 4]. -/
theorem leafB8_adjQK_pairing : kConstB8 adjQB8 = adjQB8 1 := by
  sorry

/-- LEAF: Ein x = log x + γ + E_1(x) with E_1(x) → 0, so Ein x - log x → γ as x → ∞,
Abramowitz and Stegun 5.1.39. Class HARD: needs the integral representation of the
Euler Mascheroni constant, γ = the integral over [0, 1] of (1 - e ^ -t) / t minus the
integral over [1, ∞) of e ^ -t / t. -/
theorem leafB8_ein_asymp :
    Tendsto (fun x => einB8 x - log x) atTop (𝓝 eulerMascheroniConstant) := by
  sorry

/-- LEAF: g(x) = x e ^ -Ein x is continuous at 0 from the right and, for x > 0,
g'(x) = e ^ -Ein x - x Ein'(x) e ^ -Ein x = e ^ (-x - Ein x) since
Ein'(x) = (1 - e ^ -x) / x by FTC, the integrand extending continuously to 0.
Class MEDIUM: FTC for einB8 plus continuity of the integrand. -/
theorem leafB8_ein_deriv :
    ContinuousWithinAt (fun x => x * exp (-einB8 x)) (Set.Ici 0) 0 ∧
      ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun x => x * exp (-einB8 x)) (exp (-1 * x - einB8 x)) x := by
  sorry

/-- q(1) = e ^ -γ, proved from leafB8_ein_deriv and leafB8_ein_asymp by the improper FTC. -/
theorem adjQB8_one : adjQB8 1 = exp (-eulerMascheroniConstant) := by
  obtain ⟨hc, hd⟩ := leafB8_ein_deriv
  have hlim : Tendsto (fun x => x * exp (-einB8 x)) atTop
      (𝓝 (exp (-eulerMascheroniConstant))) := by
    have h1 : Tendsto (fun x => exp (-(einB8 x - log x))) atTop
        (𝓝 (exp (-eulerMascheroniConstant))) :=
      (continuous_exp.tendsto _).comp leafB8_ein_asymp.neg
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_sub, exp_sub, exp_log hx, exp_neg, div_eq_mul_inv]
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hc hd
    (fun x _ => (exp_pos _).le) hlim
  unfold adjQB8
  rw [this]
  simp

/-- Twin of leafB8_adjQ_K, statement verbatim, proved from the three LEAFs above. -/
theorem leafB8_adjQ_K_twin : kConstB8 adjQB8 = exp (-eulerMascheroniConstant) := by
  rw [leafB8_adjQK_pairing, adjQB8_one]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_K_twin
