import LeanLab.HelfgottMajor.Decomp511b
import Mathlib

/-!
Split of `Decomp511b.positive_ray_rotation`, the contour replacement by the rotated ray `C'`
before displays 3.65 and 3.66 of page 26 of the source, into one leaf per analytic step.

The shape of the statement is the angle independence of the line integral of
`z ^ (s - 1) * exp (-z ^ 2 / 2 + 2 * pi * I * delta * z)` along the ray of angle `theta`,
together with the identification of the `theta = 0` ray with `gaussianMellin`. Writing the
ray parametrization `z = r * exp (I * theta)` gives the prefactor `exp (I * theta * s)` and
the kernel `rotatedKernel`, whose norm is already evaluated in this module.

The leaves are: the `theta = 0` identification, the continuity of the angle family at the
left endpoint `0`, the vanishing of its angle derivative on the open interval, and the
derivative of the angle prefactor. The assembly is angle constancy on the open interval
combined with the endpoint limit and the theta zero identification.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_positive_ray_rotation

open Real MeasureTheory Filter Set
open LeanLab.HelfgottArcs SplitGaussian123
open LeanLab.HelfgottMajor.Decomp511b
open scoped Topology

/-- LEAF zero angle identification. At angle zero the rotated kernel is exactly the twisted
Gaussian Mellin integrand, so the rotated ray integral is `gaussianMellin` itself. -/
theorem zero_angle_ray_eq_mellin (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) :
    (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x) = gaussianMellin δ s := by
  unfold gaussianMellin mellin rotatedKernel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  simp only [Complex.exp_zero, Complex.ofReal_zero, zero_add, one_mul]

/-- LEAF endpoint continuity of the angle family. As the angle decreases to zero from above,
the normalized rotated ray integral tends to its value at angle zero. This is the dominated
convergence step, with the Gaussian majorant coming from `rotatedKernel_norm`. -/
theorem angle_family_tendsto_zero (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) :
    Tendsto (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ φ s x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x)) := by
  sorry

/-- LEAF vanishing of the angle derivative. The normalized rotated ray integral has zero
derivative at every interior angle, which is the angle independence of the contour integral
of the twisted Gaussian exponential. -/
theorem angle_family_deriv_zero (δ : ℝ) (s : ℂ) (hσ : 0 < s.re) (φ : ℝ)
    (hφ : φ ∈ Ioo (0 : ℝ) (π / 4)) :
    HasDerivAt (fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ ψ s x)) 0 φ := by
  sorry

/-- LEAF derivative of the angle prefactor `exp (I * theta * s)` in the real angle. -/
theorem angle_prefactor_hasDerivAt (s : ℂ) (φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s))
      (Complex.I * s * Complex.exp ((φ : ℂ) * Complex.I * s)) φ := by
  have hinner : HasDerivAt (fun ψ : ℝ => (ψ : ℂ) * Complex.I * s)
      (Complex.I * s) φ := by
    convert (((hasDerivAt_id φ).ofReal_comp).mul_const Complex.I).mul_const s using 1 <;>
      simp only [id_eq, one_mul] <;> ring
  convert (Complex.hasDerivAt_exp ((φ : ℂ) * Complex.I * s)).comp φ hinner using 1 <;>
    simp only [id_eq] <;> ring

/-- The contour replacement by the rotated ray, assembled from the four leaves above.
No hypothesis of the sealed statement is dropped and no leaf is used as its hypothesis. -/
theorem positive_ray_rotation_split (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    gaussianMellin δ s = Complex.exp ((θ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x) := by
  set F : ℝ → ℂ := fun ψ : ℝ => Complex.exp ((ψ : ℂ) * Complex.I * s) *
    (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ ψ s x) with hF
  have hderiv : ∀ φ ∈ Ioo (0 : ℝ) (π / 4), HasDerivAt F 0 φ := by
    intro φ hφ
    rw [hF]
    exact angle_family_deriv_zero δ s hσ φ hφ
  have hdiff : DifferentiableOn ℝ F (Ioo (0 : ℝ) (π / 4)) := by
    intro φ hφ
    exact (hderiv φ hφ).differentiableAt.differentiableWithinAt
  have hzero : (Ioo (0 : ℝ) (π / 4)).EqOn (deriv F) 0 := by
    intro φ hφ
    exact (hderiv φ hφ).deriv
  have hconst : ∀ a ∈ Ioo (0 : ℝ) (π / 4), ∀ b ∈ Ioo (0 : ℝ) (π / 4), F a = F b :=
    fun a ha b hb => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ha hb
  have hlim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x)) := by
    rw [hF]
    exact angle_family_tendsto_zero δ s hσ
  have hlimθ : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F θ)) := by
    have hev : (fun _ : ℝ => F θ) =ᶠ[𝓝[>] (0 : ℝ)] F := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < π / 4 by linarith)).filter_mono
          nhdsWithin_le_nhds] with φ hφ hφ'
      exact (hconst φ ⟨hφ, hφ'⟩ θ ⟨hθ0, hθ1⟩).symm
    exact Tendsto.congr' hev tendsto_const_nhds
  have hEq : F θ = ∫ x : ℝ in Ioi (0 : ℝ), rotatedKernel δ 0 s x :=
    tendsto_nhds_unique hlimθ hlim0
  rw [← zero_angle_ray_eq_mellin δ s hσ, ← hEq, hF]

end LeanLab.HelfgottMajor.SPLIT_positive_ray_rotation
