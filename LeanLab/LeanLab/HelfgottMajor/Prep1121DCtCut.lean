import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
PREP split 2026-11-21, burst unit P1122-0049, ROUTE EASY: Cauchy for a removable
singularity at 0. If f is complex differentiable at every point of the punctured open
ball B(0, R) minus {0}, and assigning the value w at the junk point 0 makes
`Function.update f 0 w` continuous on the closed ball, then the circle integral of f
around C(0, R) vanishes: apply
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` to the updated
function with the countable exceptional set {0}, then transport back along the circle,
where f and its update agree because R > 0.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtCut

open Set Metric

/-- ROUTE EASY, burst unit P1122-0049: Cauchy for a removable singularity at 0, after
replacing the junk value at 0. -/
theorem circle_removable {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (w : ℂ)
    (hcont : ContinuousOn (Function.update f 0 w) (Metric.closedBall 0 R))
    (hdiff : ∀ z ∈ Metric.ball (0 : ℂ) R \ {(0 : ℂ)}, DifferentiableAt ℂ f z) :
    circleIntegral f 0 R = 0 := by
  have hs : ({(0 : ℂ)} : Set ℂ).Countable := countable_singleton _
  have hd : ∀ z ∈ Metric.ball (0 : ℂ) R \ {(0 : ℂ)},
      DifferentiableAt ℂ (Function.update f 0 w) z := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    refine (hdiff z hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact Function.update_of_ne hx0 w f
  have h0 : circleIntegral (Function.update f 0 w) 0 R = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le hs hcont hd
  have heq : EqOn f (Function.update f 0 w) (sphere 0 R) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hd : dist z (0 : ℂ) = R := hz
      rw [h, dist_self] at hd
      exact hR.ne' hd.symm
    rw [Function.update_of_ne hz0]
  calc circleIntegral f 0 R = circleIntegral (Function.update f 0 w) 0 R :=
        circleIntegral.integral_congr hR.le heq
    _ = 0 := h0

end LeanLab.HelfgottMajor.Prep1121DCtCut

#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.circle_removable
