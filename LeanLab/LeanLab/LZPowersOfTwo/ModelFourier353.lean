/-
P0079 page 10, the Fubini and Fourier identity for J of u.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

set_option maxHeartbeats 800000 in
/-- P0079 page 10, the identity defining J after display 36.
The full-line integral of two continuous box transforms against the kernel
is the double integral of the tent function of their linear form. -/
theorem continuous_pair_transform353 (a b l1 l2 u η : ℝ) (hη : 0 < η) :
    (∫ α : ℝ,
      (∫ t in Set.Icc a b, character293 (t * (l1 * α))) *
      (∫ v in Set.Icc a b, character293 (v * (l2 * α))) *
        character293 (u * α) * (kernel293 η α : ℂ)) =
      ∫ t in Set.Icc a b, ∫ v in Set.Icc a b,
        ((max 0 (η - |l1 * t + l2 * v + u|) : ℝ) : ℂ) := by
  let ν : Measure ℝ := volume.restrict (Set.Icc a b)
  let F : (ℝ × ℝ) → ℝ → ℂ := fun z α =>
    character293 ((l1 * z.1 + l2 * z.2 + u) * α) * kernel293 η α
  have hdom : Integrable (fun z : (ℝ × ℝ) × ℝ => kernel293 η z.2)
      ((ν.prod ν).prod volume) := by
    simpa using (integrable_const (μ := ν.prod ν) (1 : ℝ)).mul_prod (kernel_integrable293 η)
  have hc : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    unfold character293 kernel293
    fun_prop
  have hf : Integrable (Function.uncurry F) ((ν.prod ν).prod volume) := by
    apply hdom.mono' hc.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    simp only [F, Function.uncurry, norm_mul, character_norm293,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η z.2), one_mul, le_refl]
  have hbox (α : ℝ) : Integrable (fun z : ℝ × ℝ => F z α) (ν.prod ν) := by
    have hc' : Continuous (fun z : ℝ × ℝ => F z α) := by
      dsimp [F]
      unfold character293 kernel293
      fun_prop
    apply (integrable_const (μ := ν.prod ν) (kernel293 η α)).mono' hc'.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    simp only [F, norm_mul, character_norm293, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α), one_mul, le_refl]
  have hphase (t v α : ℝ) : F (t, v) α =
      character293 (t * (l1 * α)) * character293 (v * (l2 * α)) *
        character293 (u * α) * (kernel293 η α : ℂ) := by
    dsimp [F]
    rw [show (l1 * t + l2 * v + u) * α =
      t * (l1 * α) + v * (l2 * α) + u * α by ring]
    rw [character_add293, character_add293]
  have hT : Integrable (fun z : ℝ × ℝ =>
      ((max 0 (η - |l1 * z.1 + l2 * z.2 + u|) : ℝ) : ℂ)) (ν.prod ν) := by
    apply hf.integral_prod_left.congr
    apply Eventually.of_forall
    intro z
    exact kernel_transform293 η (l1 * z.1 + l2 * z.2 + u) hη
  calc
    _ = ∫ α : ℝ, ∫ z : ℝ × ℝ, F z α ∂ν.prod ν := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro α
      dsimp only
      rw [integral_prod _ (hbox α)]
      simp_rw [hphase, integral_mul_const, integral_const_mul]
      rw [integral_mul_const]
    _ = ∫ z : ℝ × ℝ, ∫ α : ℝ, F z α ∂volume ∂ν.prod ν :=
      (integral_integral_swap hf).symm
    _ = ∫ z : ℝ × ℝ, ((max 0 (η - |l1 * z.1 + l2 * z.2 + u|) : ℝ) : ℂ) ∂ν.prod ν := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => kernel_transform293 η (l1 * z.1 + l2 * z.2 + u) hη)
    _ = _ := integral_prod _ hT

end LeanLab.LZPowersOfTwo
