/-
Split of the one-zero target `hardy_critical_line_zero150`: one zero of the zeta
function on the critical line.

Route.  The real function `Xi` of the completed zeta function vanishes exactly where
the zeta function vanishes on the critical line, and it is continuous.  Two points
where `Xi` has opposite signs therefore give a zero by the intermediate value
theorem.  The signs are forced by the limits of the zeroth and the first weighted
moment of `Xi` as the parameter approaches the theta cusp from below.  Those two
limits rest on (i) the base Mellin transform of the moment at order zero and (ii) the
identification of the second derivative of that transform with the moment at order
one.

Both leaves use the existing open Mellin inputs in Decomp515a.
The assembly below is conditional on those inputs and does not use the target.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ZeroBoundLeaf150

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory Set
open Complex

/-- CONDITIONAL on hardy_mellin_base515. The base Mellin transform, at order zero, of the weighted moment of `Xi`:
inside the strip the moment equals the cosine main term minus the theta correction.
This is one identity in the parameter, and it is the transform step alone, with no
differentiated moment. -/
theorem hardy_mellin_base150 (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyMoment515 0 α = Real.pi * Real.cos (α / 4) - hardyThetaCorrection515 α := by
  exact hardy_mellin_base515 α hα

/-- CONDITIONAL on hardy_mellin_differentiation515. The differentiation step at order one: differentiating the moment of order
zero twice gives the moment of order one, inside the strip.  This is one identity,
strictly weaker than the general even-order statement since only order one is asked. -/
theorem hardy_moment_second_derivative150 (α : ℝ) (hα : |α| < Real.pi / 2) :
    iteratedDeriv 2 (hardyMoment515 0) α = hardyMoment515 1 α := by
  simpa only [Nat.mul_one] using (hardy_mellin_differentiation515 1 α hα).2

/-- The order one transform identity, from the two leaves above by the derivative
test: near a point of the strip the theta correction is the cosine main term minus the
order zero moment, so its second derivative is the second derivative of that
difference. -/
theorem hardy_mellin_identity_one150 (α : ℝ) (hα : |α| < Real.pi / 2) :
    hardyMoment515 1 α =
      (-1 : ℝ) ^ 1 * Real.pi / 4 ^ (2 * 1) * Real.cos (α / 4) -
        iteratedDeriv (2 * 1) hardyThetaCorrection515 α := by
  have ho : {β : ℝ | |β| < Real.pi / 2} ∈ 𝓝 α :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hα
  have he : hardyThetaCorrection515 =ᶠ[𝓝 α]
      (fun β : ℝ => Real.pi * Real.cos (β / 4) - hardyMoment515 0 β) := by
    filter_upwards [ho] with β hβ
    have hb := hardy_mellin_base150 β hβ
    linarith
  have hcont : ContDiffAt ℝ (2 * 1) (hardyMoment515 0) α := by
    have he2 : hardyMoment515 0 =ᶠ[𝓝 α]
        (fun β : ℝ => Real.pi * Real.cos (β / 4) - hardyThetaCorrection515 β) := by
      filter_upwards [ho] with β hβ
      exact hardy_mellin_base150 β hβ
    exact ((by fun_prop : ContDiffAt ℝ (2 * 1)
      (fun β : ℝ => Real.pi * Real.cos (β / 4)) α).sub
      (contDiffAt_hardyThetaCorrection515 (2 * 1) α hα)).congr_of_eventuallyEq he2
  have h2 : iteratedDeriv (2 * 1) (hardyMoment515 0) α = hardyMoment515 1 α := by
    simpa using hardy_moment_second_derivative150 α hα
  have hh := he.iteratedDeriv_eq (2 * 1)
  rw [iteratedDeriv_fun_sub (by fun_prop) hcont, hardy_cos_iteratedDeriv515, h2] at hh
  linarith

/-- Split assembly: one zero of the zeta function on the critical line, from the two
leaves above and the sorry free continuity, sign and moment bookkeeping. -/
theorem hardy_critical_line_zero150_split :
    ∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have hzero : Tendsto (hardyMoment515 0) (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi * Real.cos (Real.pi / 8))) := by
    simpa using hardy_moment_limit_of515 0
      (fun α hα => by simpa using hardy_mellin_base150 α hα)
      (by simpa using hardy_theta_flat_zero515)
  have hone : Tendsto (hardyMoment515 1) (𝓝[<] (Real.pi / 2))
      (𝓝 (-Real.pi / 16 * Real.cos (Real.pi / 8))) := by
    simpa only [Nat.mul_one, pow_one, neg_one_mul,
      show (4 : ℝ) ^ 2 = 16 by norm_num] using
      hardy_moment_limit_of515 1 hardy_mellin_identity_one150 (hardy_theta_flat515 1)
  obtain ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩ := hardyXi_signs_of_moment_limits515 hzero hone
  exact hardy_zero_of_signs515 ha hb

end LeanLab.BhowmikGrimmelt2026
