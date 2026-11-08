import Mathlib.Analysis.Fourier.Convolution
import LeanLab.ExceptionalSet.Decomp450j
import LeanLab.ExceptionalSet.KernelTail385

/-!
P0082 page 356, a reproducing kernel auxiliary for the generic sampling input.
The exact convolution identity is proved from Mathlib Fourier inversion.
The missing uniform lattice estimate is not assumed or claimed here.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464g

open Real MeasureTheory
open scoped FourierTransform Convolution
open LeanLab.ExceptionalSet.U1539 (Kfun ftR)

/-- P0082 page 356 displays 2 and 3, a dilation auxiliary for Lemma 1.
Doubling the spatial scale widens the transform plateau beyond the unit interval. -/
theorem wide_kernel_fourier (ξ : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 4) (2 * x) : ℂ)) ξ =
      (KernelTransform264.weight (1 / 4) (ξ / 2) : ℂ) := by
  have hscale : FourierTransform.fourier
      (fun x : ℝ => (2 : ℂ) * (Kfun (1 / 4) (2 * x) : ℂ)) ξ =
      (2 : ℂ) * FourierTransform.fourier
        (fun x : ℝ => (Kfun (1 / 4) (2 * x) : ℂ)) ξ := by
    simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hd := TriangleKernel264.fourier_comp_pos_mul
    (fun t : ℝ => (Kfun (1 / 4) t : ℂ)) (by norm_num : (0 : ℝ) < 2) ξ
  rw [hscale, hd,
    KernelTransform264.fourier_Kfun (by norm_num) (by norm_num)]
  norm_num <;> ring

/-- P0082 page 356, auxiliary reproducing identity for the bandlimited kernel.
The wider explicit kernel has transform one on the transform support of K.
This proves the convolution identity only. The uniform lattice bound is separate. -/
theorem bandlimited_reproducing_convolution (K : ℝ → ℂ) (hK : Integrable K)
    (hcont : Continuous K) (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) (x : ℝ) :
    (∫ y : ℝ, K y * ((2 : ℂ) * (Kfun (1 / 4) (2 * (x - y)) : ℂ))) = K x := by
  let H : ℝ → ℂ := fun y => (2 : ℂ) * (Kfun (1 / 4) (2 * y) : ℂ)
  let C : ℝ → ℂ := K ⋆[ContinuousLinearMap.mul ℂ ℂ] H
  have hHi : Integrable H :=
    ((KernelTransform264.Kfun_integrable (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).comp_mul_left'
        (by norm_num : (2 : ℝ) ≠ 0)).const_mul (2 : ℂ)
  have hHc : Continuous H := continuous_const.mul
    ((KernelTransform264.Kfun_continuous (1 / 4)).comp (continuous_const.mul continuous_id))
  have hHb : BddAbove (Set.range fun y => ‖H y‖) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hk := KernelTail385.kernel_abs_le_two_sub (1 / 4) (2 * y)
      (by norm_num) (by norm_num)
    dsimp only [H]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    linarith
  have hCi : Integrable C := hK.integrable_convolution
    (L := ContinuousLinearMap.mul ℂ ℂ) hHi
  have hCc : Continuous C :=
    BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) hHb hK hHc
  have hFeq : FourierTransform.fourier C = FourierTransform.fourier K := by
    funext ξ
    change FourierTransform.fourier (K ⋆[ContinuousLinearMap.mul ℂ ℂ] H) ξ = _
    rw [Real.fourier_mul_convolution_eq hK hHi]
    by_cases hξ : |ξ| ≤ 1
    · have hw : KernelTransform264.weight (1 / 4) (ξ / 2) = 1 := by
        apply KernelTransform264.weight_one (by norm_num) (by norm_num)
        rw [abs_div]
        norm_num
        linarith
      have hwide : FourierTransform.fourier H ξ =
          (KernelTransform264.weight (1 / 4) (ξ / 2) : ℂ) := wide_kernel_fourier ξ
      rw [hwide, hw, Complex.ofReal_one, mul_one]
    · have hz : FourierTransform.fourier K ξ = 0 := by
        rw [← Decomp404b.ftR_eq_fourier]
        exact hsupp ξ (lt_of_not_ge hξ)
      rw [hz, zero_mul]
  have hFi : Integrable (FourierTransform.fourier K) :=
    Decomp450j.bandlimited_fourier_integrable K hK hsupp
  have hCFi : Integrable (FourierTransform.fourier C) := hFeq.symm ▸ hFi
  have hCK : C = K := by
    calc
      C = FourierTransformInv.fourierInv (FourierTransform.fourier C) :=
        (hCc.fourierInv_fourier_eq hCi hCFi).symm
      _ = FourierTransformInv.fourierInv (FourierTransform.fourier K) := by rw [hFeq]
      _ = K := hcont.fourierInv_fourier_eq hK hFi
  change C x = K x
  exact congrFun hCK x

end LeanLab.ExceptionalSet.Decomp464g
