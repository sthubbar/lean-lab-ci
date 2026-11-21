import LeanLab.HelfgottMajor.Route669
import LeanLab.HelfgottMajor.Principal457
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
The conductor one case of the circle residue leaf.
Source P0014 page 33 after display 4.9 and page 34.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Residue669
open Real Complex MeasureTheory Set Filter
open MainLemma41Split123
open scoped Topology

/-- P0014 pages 33 and 34. At conductor one the circle residue is log of two pi,
for every allowed radius, every shift and every x at least one. -/
theorem residue_at_zero_conductor_one (x : ℝ) (hx : 1 ≤ x)
    (χ : DirichletCharacter ℂ 1) (δ r : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0})) :
    (2 * π * I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
      ((log (2 * π) : ℝ) : ℂ) := by
  have hχ : χ = 1 := Subsingleton.elim _ _
  subst χ
  let F := contourIntegrand (1 : DirichletCharacter ℂ 1) δ x
  have hx0 : 0 < x := by linarith
  have hz : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by simp)
  have hl : ContinuousAt (logDeriv riemannZeta) 0 :=
    (hz.deriv.div hz (by rw [riemannZeta_zero]; norm_num)).continuousAt
  have hp : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (continuousAt_const_cpow (by exact_mod_cast hx0.ne') :
      ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0).tendsto.mono_left nhdsWithin_le_nhds
  have hy : Tendsto (fun s : ℂ => s * F s) (𝓝[≠] 0)
      (𝓝 ((log (2 * π) : ℝ) : ℂ)) := by
    have hlim := ((hl.tendsto.mono_left nhdsWithin_le_nhds).mul
      (Route669.contMellin_residue_one δ)).mul hp
    rw [Principal457.zeta_logDeriv_zero] at hlim
    simp only [mul_one] at hlim
    apply hlim.congr'
    filter_upwards [] with s
    simp only [F, contourIntegrand, DirichletCharacter.LFunction_modOne_eq, logDeriv_apply]
    ring
  have hc : ContinuousOn (fun s : ℂ => s * F s) (Metric.closedBall 0 r \ {0}) :=
    continuousOn_id.mul hF.continuousOn
  have hd : ∀ z ∈ (Metric.ball (0 : ℂ) r \ {0}) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun s : ℂ => s * F s) z := by
    intro z hz
    have hsub : Metric.ball (0 : ℂ) r \ {0} ⊆ Metric.closedBall 0 r \ {0} :=
      sdiff_subset_sdiff_left Metric.ball_subset_closedBall
    have hdiff := (hF.mono hsub).differentiableAt
      ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hz.1)
    exact differentiableAt_id.mul hdiff
  have hcircle :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hr (countable_empty : (∅ : Set ℂ).Countable) hc hd hy
  have heq : (circleIntegral (fun z : ℂ => (z - 0)⁻¹ • (z * F z)) 0 r) =
      circleIntegral F 0 r := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzR : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by
      intro h
      simp only [h, norm_zero] at hzR
      linarith
    simp only [sub_zero, smul_eq_mul, inv_mul_cancel_left₀ hz0]
    rfl
  rw [heq] at hcircle
  change (2 * π * I)⁻¹ * circleIntegral F 0 r = _
  rw [hcircle, smul_eq_mul, inv_mul_cancel_left₀ (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero)) I_ne_zero)]

end LeanLab.HelfgottMajor.Residue669

#print axioms LeanLab.HelfgottMajor.Residue669.residue_at_zero_conductor_one
