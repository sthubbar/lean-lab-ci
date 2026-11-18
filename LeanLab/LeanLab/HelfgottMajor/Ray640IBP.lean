import LeanLab.HelfgottMajor.Decomp511b

/-!
P0014 page 26, display 3.67.
Transfer the proved real ray integration by parts to the rotated ray.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Ray640IBP
open Real MeasureTheory Set
open LeanLab.HelfgottArcs SplitGaussian123 Decomp511b

/-- The rotated Mellin integral including its angular Jacobian.
P0014 page 26 before display 3.66 and in display 3.67. -/
noncomputable def rayMellin (δ θ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I * s) *
    (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x)

/-- LEAF: The normalized rotated integral equals the shared Mellin transform.
P0014 page 26 before display 3.66. This is the proved rotation identity. -/
theorem rayMellin_eq (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    rayMellin δ θ s = gaussianMellin δ s := by
  exact (positive_ray_rotation δ θ s hδ hσ ht hθ0 hθ1).symm

/-- LEAF: Integration by parts on the rotated ray, with both raised arguments retained.
P0014 page 26 display 3.67. The existing real ray recurrence is reused. -/
theorem rayMellin_recurrence (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    s * rayMellin δ θ s = rayMellin δ θ (s + 2) -
      (2 * Real.pi * Complex.I * δ) * rayMellin δ θ (s + 1) := by
  rw [rayMellin_eq δ θ s hδ hσ ht hθ0 hθ1,
    rayMellin_eq δ θ (s + 2) hδ (by simp; linarith) (by simpa) hθ0 hθ1,
    rayMellin_eq δ θ (s + 1) hδ (by simp; linarith) (by simpa) hθ0 hθ1]
  exact twisted_mellin_recurrence δ s hσ

/-- LEAF: The integration by parts norm bound on the rotated ray.
P0014 page 26 display 3.67 and page 27. No new Gamma estimate is assumed. -/
theorem rayMellin_recurrence_norm (δ θ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    ‖rayMellin δ θ s‖ ≤
      (‖rayMellin δ θ (s + 2)‖ + (2 * π * |δ|) * ‖rayMellin δ θ (s + 1)‖) / ‖s‖ := by
  rw [rayMellin_eq δ θ s hδ hσ ht hθ0 hθ1,
    rayMellin_eq δ θ (s + 2) hδ (by simp; linarith) (by simpa) hθ0 hθ1,
    rayMellin_eq δ θ (s + 1) hδ (by simp; linarith) (by simpa) hθ0 hθ1]
  exact twisted_recurrence_norm δ s hσ

end LeanLab.HelfgottMajor.Ray640IBP
