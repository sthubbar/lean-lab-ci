import LeanLab.HelfgottMajor.LogResidue669
import LeanLab.HelfgottMajor.Residue669

/-!
The circle residue of the general primitive character integrand.
Source P0014 pages 32 to 34, displays 4.6 to 4.9, with the scale factor retained.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.CircleResidue669
open Real Complex MeasureTheory Set Filter Classical
open MainLemma41Split123
open scoped Topology

/-- P0014 page 33, displays 4.6 and 4.7. A function holomorphic on the punctured disc,
whose regularized double pole has the given constant limit, has that normalized circle residue. -/
theorem circle_residue_of_regular_limit (F : ℂ → ℂ) (a R : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 r \ {0}))
    (hlim : Tendsto (fun s : ℂ => s * F s - a / s) (𝓝[≠] 0) (𝓝 R)) :
    (2 * π * I)⁻¹ * circleIntegral F 0 r = R := by
  have hnz (z : ℂ) (hz : z ∈ Metric.sphere 0 r) : z ≠ 0 := by
    intro hz0
    subst z
    simpa [Metric.mem_sphere, hr.ne', hr.ne] using hz
  have hsub : Metric.sphere (0 : ℂ) r ⊆ Metric.closedBall 0 r \ {0} := by
    intro z hz
    exact ⟨Metric.sphere_subset_closedBall hz, by simpa only [mem_singleton_iff] using hnz z hz⟩
  have hIntF : CircleIntegrable F 0 r :=
    (hF.continuousOn.mono hsub).circleIntegrable hr.le
  have hzero : (0 : ℂ) ∉ Metric.sphere 0 |r| := by
    simp [Metric.mem_sphere, abs_of_pos hr, hr.ne', hr.ne]
  have hIntP : CircleIntegrable (fun z : ℂ => (z - 0) ^ (-2 : ℤ)) 0 r :=
    circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hzero))
  have hIntA : CircleIntegrable (fun z : ℂ => a * (z - 0) ^ (-2 : ℤ)) 0 r := by
    simpa only [Pi.mul_apply] using! hIntP.continuousOn_mul
      (g := fun _ => a) continuousOn_const
  have hc : ContinuousOn (fun z : ℂ => z * F z - a / z) (Metric.closedBall 0 r \ {0}) :=
    (continuousOn_id.mul hF.continuousOn).sub
      (continuousOn_const.div continuousOn_id (fun z hz => by
        simpa only [mem_singleton_iff] using hz.2))
  have hd : ∀ z ∈ (Metric.ball (0 : ℂ) r \ {0}) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun s : ℂ => s * F s - a / s) z := by
    intro z hz
    have hsubs : Metric.ball (0 : ℂ) r \ {0} ⊆ Metric.closedBall 0 r \ {0} :=
      sdiff_subset_sdiff_left Metric.ball_subset_closedBall
    have hdiff := (hF.mono hsubs).differentiableAt
      ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hz.1)
    have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hz.1.2
    exact (differentiableAt_id.mul hdiff).sub
      ((differentiableAt_const a).div differentiableAt_id hz0)
  have hcircle :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hr (countable_empty : (∅ : Set ℂ).Countable) hc hd hlim
  have heq : circleIntegral (fun z : ℂ => (z - 0)⁻¹ • (z * F z - a / z)) 0 r =
      circleIntegral F 0 r := by
    calc
      _ = circleIntegral (fun z : ℂ => F z - a * (z - 0) ^ (-2 : ℤ)) 0 r := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hz0 := hnz z hz
        norm_num only [sub_zero, smul_eq_mul, zpow_neg, zpow_ofNat]
        field_simp
        <;> ring
      _ = _ := by
        rw [circleIntegral.integral_sub hIntF hIntA, circleIntegral.integral_const_mul,
          circleIntegral.integral_sub_zpow_of_ne (by norm_num : (-2 : ℤ) ≠ -1),
          mul_zero, sub_zero]
  rw [heq] at hcircle
  rw [hcircle, smul_eq_mul, inv_mul_cancel_left₀ (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero)) I_ne_zero)]

/-- P0014 pages 33 and 34, displays 4.6 to 4.9. The regularized contour integrand has
constant term equal to the corrected residue, including the even character log x. -/
theorem integrand_regular_limit (x : ℝ) (hx : 1 ≤ x) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) :
    Tendsto (fun s : ℂ => s * contourIntegrand χ δ x s -
      (if χ.Even then (1 : ℂ) else 0) / s) (𝓝[≠] 0)
      (𝓝 (((((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ)) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1)) +
        (if χ.Even then ((Real.log x : ℝ) : ℂ) + laurentC0 δ else 0))) := by
  let a : ℂ := if χ.Even then 1 else 0
  let A : ℂ := ((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
    (starRingEnd ℂ) (logDeriv (DirichletCharacter.LFunction χ) 1)
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have ha (s : ℂ) : a / s = if χ.Even then 1 / s else 0 := by
    dsimp only [a]
    split_ifs <;> simp
  have hL : Tendsto (fun s : ℂ => logDeriv (DirichletCharacter.LFunction χ) s - a / s)
      (𝓝[≠] 0) (𝓝 A) := by
    simp_rw [ha]
    exact LogResidue669.logDeriv_regular_limit χ hχ hq
  have hG1 := Route669.contMellin_residue_one δ
  have hG0 := Laurent669.contMellin_sub_pole_tendsto δ
  have hX : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (continuousAt_const_cpow hxc :
      ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0).tendsto.mono_left nhdsWithin_le_nhds
  have hdX : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) (Real.log x : ℂ) 0 := by
    have hh := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hxc)
    simpa only [id_eq, cpow_zero, one_mul, mul_one, ← Complex.ofReal_log hx0.le] using hh
  have hDX := hdX.tendsto_slope_zero
  simp only [zero_add, cpow_zero, smul_eq_mul] at hDX
  have hXd : Tendsto (fun s : ℂ => ((x : ℂ) ^ s - 1) / s)
      (𝓝[≠] 0) (𝓝 (Real.log x : ℂ)) := by
    apply hDX.congr'
    filter_upwards [] with s
    simp only [div_eq_mul_inv]
    ring
  have hlim := ((hL.mul hG1).mul hX).add ((hG0.mul hX).const_mul a)
    |>.add (hXd.const_mul a)
  have hv : A * 1 * 1 + a * (laurentC0 δ * 1) + a * (Real.log x : ℂ) =
      A + (if χ.Even then ((Real.log x : ℝ) : ℂ) + laurentC0 δ else 0) := by
    dsimp only [a]
    split_ifs <;> ring
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change s ≠ 0 at hs
  change (logDeriv (DirichletCharacter.LFunction χ) s - a / s) *
      (s * contMellin δ s) * (x : ℂ) ^ s +
      a * ((contMellin δ s - 1 / s) * (x : ℂ) ^ s) +
      a * (((x : ℂ) ^ s - 1) / s) =
    s * (logDeriv (DirichletCharacter.LFunction χ) s * contMellin δ s * (x : ℂ) ^ s) - a / s
  generalize logDeriv (DirichletCharacter.LFunction χ) s = l
  generalize contMellin δ s = g
  generalize (x : ℂ) ^ s = X
  field_simp
  <;> ring

/-- P0014 pages 33 and 34, displays 4.6 to 4.9, with the corrected scale factor and
conjugate. The exact circle residue for every primitive character. -/
theorem residue_at_zero_general (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ r : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0})) :
    (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
      (if q = 1 then ((Real.log (2 * π) : ℝ) : ℂ) else
          ((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
            (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
              DirichletCharacter.LFunction χ 1)) +
        (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) + laurentC0 δ else 0) := by
  by_cases hq : q = 1
  · subst q
    simpa using Residue669.residue_at_zero_conductor_one x hx χ δ r hr hF
  · have hlim := integrand_regular_limit x hx χ hχ hq δ
    have hcircle := circle_residue_of_regular_limit (contourIntegrand χ δ x)
      (if χ.Even then 1 else 0)
      (((((Real.log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ)) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1)) +
        (if χ.Even then ((Real.log x : ℝ) : ℂ) + laurentC0 δ else 0)) r hr hF hlim
    simpa [hq] using hcircle

end LeanLab.HelfgottMajor.CircleResidue669

#print axioms LeanLab.HelfgottMajor.CircleResidue669.circle_residue_of_regular_limit

#print axioms LeanLab.HelfgottMajor.CircleResidue669.integrand_regular_limit
#print axioms LeanLab.HelfgottMajor.CircleResidue669.residue_at_zero_general
