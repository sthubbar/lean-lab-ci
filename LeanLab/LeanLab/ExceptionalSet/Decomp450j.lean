import LeanLab.ExceptionalSet.Decomp450a

/-!
P0082 page 356, auxiliary Fourier inversion input for the bandlimited kernel.
Source: https://doi.org/10.5802/aif.1621
Integrability and compact Fourier support make the Fourier transform integrable.
This is a clean prerequisite for the remaining translate norm estimate.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450j

open Real MeasureTheory
open scoped FourierTransform
open LeanLab.ExceptionalSet.U1539 (ftR)

/-- P0082 page 356, auxiliary integrability of the compactly supported transform.
Continuity of the original kernel is not required for this step. -/
theorem bandlimited_fourier_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
    Integrable (FourierTransform.fourier K) := by
  have hct : Continuous (FourierTransform.fourier K) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ ℝ) continuous_inner hK
  have hsupport : Function.support (FourierTransform.fourier K) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro ξ hξ
    by_contra hout
    have hlarge : 1 < |ξ| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hout
      rcases hout with hlo | hhi
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hhi
    apply hξ
    rw [← Decomp404b.ftR_eq_fourier]
    exact hsupp ξ hlarge
  apply hct.integrable_of_hasCompactSupport
  rw [hasCompactSupport_def]
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsupport isClosed_Icc)

end LeanLab.ExceptionalSet.Decomp450j
