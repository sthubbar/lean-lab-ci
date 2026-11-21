import LeanLab.HelfgottMajor.Residue669
import LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

/-!
The conductor one contour shift with the actual circle residue.
Source P0014 pages 32 and 33, displays 4.4 and 4.7.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PrincipalRoute669
open Real Complex MeasureTheory Set Filter
open MainLemma41Split123 LeanLab.HelfgottArcs SplitGaussian123 Contour457
open scoped Topology

/-- P0014 pages 32 and 33. At conductor one the punctured disc required by the route
exists for every shift and every x at least one. -/
theorem small_disc_conductor_one (x : ℝ) (hx : 1 ≤ x)
    (χ : DirichletCharacter ℂ 1) (δ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) := by
  have hχ : χ = 1 := Subsingleton.elim _ _
  subst χ
  have hx0 : 0 < x := by linarith
  have hz : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by simp)
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta) 0 :=
    hz.deriv.div hz (by rw [riemannZeta_zero]; norm_num)
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hlog
  have hsmall : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hlog.and hsmall)
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hsr := hsub hs.1
  have hs0 : s ≠ 0 := by simpa only [mem_singleton_iff] using hs.2
  have hd := ((hsr.1).mul (Route669.contMellin_differentiableAt δ s hsr.2 hs0)).mul
    (differentiableAt_id.const_cpow (c := (x : ℂ)) (Or.inl (by exact_mod_cast hx0.ne')))
  have hfun : contourIntegrand (1 : DirichletCharacter ℂ 1) δ x =
      fun z => logDeriv riemannZeta z * contMellin δ z * (x : ℂ) ^ z := by
    funext z
    simp only [contourIntegrand, DirichletCharacter.LFunction_modOne_eq, logDeriv_apply]
  rw [hfun]
  simpa only [Pi.mul_apply, id_eq] using!
    hd.differentiableWithinAt (s := Metric.closedBall 0 r \ {0})

/-- P0014 pages 32 and 33, displays 4.4 and 4.7. The full conductor one case of the
contour shift leaf, with the circle residue and both zero sums retained. -/
theorem contour_shift_conductor_one (x : ℝ) (hx : 1 ≤ x)
    (χ : DirichletCharacter ℂ 1) (δ T : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) ∧
      Schi etaHeart χ δ x - fhat etaHeart (-δ) * x +
          lowZeros χ δ x T + highZeros χ δ x T +
          (2 * π * I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
        -((2 * π : ℂ)⁻¹ *
          ∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * I)) := by
  have hχ : χ = 1 := Subsingleton.elim _ _
  subst χ
  obtain ⟨r, hr, hF⟩ := small_disc_conductor_one x hx 1 δ
  refine ⟨r, hr, hF, ?_⟩
  rw [Residue669.residue_at_zero_conductor_one x hx 1 δ r hr hF]
  have hshift := SPLIT_principal_contour_identity.principal_explicit_formula_shift
    x hx 1 (1 : DirichletCharacter ℂ 1) δ T rfl
  have heq : principalContour δ x = (2 * π : ℂ)⁻¹ *
      ∫ τ : ℝ, contourIntegrand (1 : DirichletCharacter ℂ 1) δ x (-1 / 2 + τ * I) := by
    simp only [principalContour, one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with τ
    rw [contourIntegrand, DirichletCharacter.LFunction_modOne_eq,
      Route669.contMellin_eq δ _ (by norm_num [Complex.mul_re])]
    rfl
  rw [heq, if_pos rfl] at hshift
  rw [show lowZeros (1 : DirichletCharacter ℂ 1) δ x T =
      Decomp269a.lowZeros 1 δ x T from rfl,
    show highZeros (1 : DirichletCharacter ℂ 1) δ x T =
      Decomp269a.highZeros 1 δ x T from rfl]
  linear_combination hshift

end LeanLab.HelfgottMajor.PrincipalRoute669

#print axioms LeanLab.HelfgottMajor.PrincipalRoute669.small_disc_conductor_one
#print axioms LeanLab.HelfgottMajor.PrincipalRoute669.contour_shift_conductor_one
