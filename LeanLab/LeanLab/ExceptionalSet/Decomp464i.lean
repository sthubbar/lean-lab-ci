import LeanLab.ExceptionalSet.Decomp464h
import LeanLab.ExceptionalSet.Decomp450b

/-!
P0082 page 356, absolute convergence of local integer translates.
A wider explicit reproducer supplies the generic bandlimited kernel estimate.
No new analytic hypothesis or admitted statement is used.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464i

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Kfun ftR eC hcheck)

/-- P0082 page 356, the exact local absolute convergence input for Lemma 1.
The wider explicit reproducer has summable compact translates by quadratic decay.
The convolution estimate transfers this to every continuous bandlimited L1 kernel. -/
theorem leaf_translate_norm_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
    ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  let H : ℝ → ℂ := fun y => (2 : ℂ) * (Kfun (1 / 4) (2 * y) : ℂ)
  have hHc : Continuous H := continuous_const.mul
    ((KernelTransform264.Kfun_continuous (1 / 4)).comp (continuous_const.mul continuous_id))
  have hHnorm (S : TopologicalSpace.Compacts ℝ) :
      Summable (fun n : ℤ =>
        ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    let T : TopologicalSpace.Compacts ℝ :=
      ⟨(fun x : ℝ => 2 * x) '' (S : Set ℝ),
        S.isCompact.image (continuous_const.mul continuous_id)⟩
    let M : ℤ → ℝ := fun n =>
      ‖((⟨fun x : ℝ => (Kfun (1 / 4) x : ℂ),
        KernelTransform264.Kfun_continuous (1 / 4)⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight (n : ℝ))).restrict T‖
    have hM : Summable M :=
      Decomp450a.kernel_translate_norm (1 / 4) (by norm_num) (by norm_num) T
    have hinj : Function.Injective (fun n : ℤ => 2 * n) := by
      intro a b hab
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hab
    have hME : Summable (fun n : ℤ => 2 * M (2 * n)) :=
      (hM.comp_injective hinj).mul_left 2
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hME
    apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _))).mpr
    intro x
    change ‖(2 : ℂ) * (Kfun (1 / 4) (2 * ((x : ℝ) + (n : ℝ))) : ℂ)‖ ≤ 2 * M (2 * n)
    rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have he : 2 * ((x : ℝ) + (n : ℝ)) =
        2 * (x : ℝ) + ((2 * n : ℤ) : ℝ) := by
      push_cast
      ring
    rw [he]
    exact ContinuousMap.norm_coe_le_norm
      (((⟨fun y : ℝ => (Kfun (1 / 4) y : ℂ),
        KernelTransform264.Kfun_continuous (1 / 4)⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight ((2 * n : ℤ) : ℝ))).restrict T)
      ⟨2 * (x : ℝ), ⟨(x : ℝ), x.property, rfl⟩⟩
  intro S
  exact Decomp464h.convolution_translate_norm K H hK hcont hHc hHnorm
    (fun x => (Decomp464g.bandlimited_reproducing_convolution K hK hcont hsupp x).symm) S

end LeanLab.ExceptionalSet.Decomp464i
