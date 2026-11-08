import LeanLab.ExceptionalSet.Decomp450j
import Mathlib.Analysis.Fourier.Convolution

/-!
P0082 page 356, auxiliary analytic justification of the Poisson display.
Source: https://doi.org/10.5802/aif.1621
This supplies the convolution step of SPLIT_leaf_kernel_sup_summable.
It does not supply the smoothing factor or its uniform lattice norm bound.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462b

open Real MeasureTheory
open scoped FourierTransform Convolution
open LeanLab.ExceptionalSet.U1539 (ftR)

/-- P0082 page 356, auxiliary reproducing convolution for the sampling argument.
This is the exact leaf_split_conv_eq statement with a new name.
An integrable factor whose transform is one on the kernel frequency support
reproduces the continuous integrable kernel at every point. -/
theorem split_conv_eq_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hφhat : ∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) :
    ∀ t : ℝ, (∫ y : ℝ, φ (t - y) * K y) = K t := by
  have hKi := Decomp450j.bandlimited_fourier_integrable K hK hsupp
  have hinv := hcont.fourierInv_fourier_eq hK hKi
  have hbound : BddAbove (Set.range fun x => ‖K x‖) := by
    refine ⟨∫ ξ : ℝ, ‖FourierTransform.fourier K ξ‖, ?_⟩
    rintro y ⟨x, rfl⟩
    change ‖K x‖ ≤ _
    calc
      _ = ‖FourierTransform.fourierInv (FourierTransform.fourier K) x‖ :=
        congrArg norm (congrFun hinv x).symm
      _ = ‖FourierTransform.fourier (FourierTransform.fourier K) (-x)‖ :=
        congrArg norm (Real.fourierInv_eq_fourier_neg _ _)
      _ ≤ _ := Real.norm_fourier_le_integral_norm _ _
  let g := φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K
  have hgc : Continuous g := hbound.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hφ hcont
  have hgi : Integrable g := hφ.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hK
  have hhat : FourierTransform.fourier g = FourierTransform.fourier K := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq hφ hK]
    by_cases hle : |ξ| ≤ 1
    · rw [← Decomp404b.ftR_eq_fourier φ ξ, hφhat ξ hle, one_mul]
    · rw [← Decomp404b.ftR_eq_fourier K ξ, hsupp ξ (lt_of_not_ge hle), mul_zero]
  have hginv := hgc.fourierInv_fourier_eq hgi (by rw [hhat]; exact hKi)
  intro t
  calc
    _ = g t := by
      change _ = (φ ⋆[ContinuousLinearMap.mul ℂ ℂ] K) t
      rw [convolution_eq_swap]
      rfl
    _ = K t := by
      rw [← hginv, hhat, hinv]

end LeanLab.ExceptionalSet.Decomp462b
