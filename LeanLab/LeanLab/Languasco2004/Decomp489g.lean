/-
PP1993 page 44 display 3, the finite Fourier kernel comparison.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The Parseval and prime weight steps are separate clean support.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.FiniteParseval489
import LeanLab.Languasco2004.CoefficientGlue489
import LeanLab.Languasco2004.Decomp531a

namespace LeanLab.Languasco2004.Decomp489g
open Finset Real MeasureTheory Decomp279b Decomp413a
noncomputable section

/-- LEAF. Page 44 display 3, before Parseval and prime weight estimates.
The finite even frequency kernel comparison and its integral
Cauchy Schwarz connection are expressed using only the minor S1 and S2
squared integrals. This has no density or prime weight input. -/
theorem finite_kernel_energy :
    ∀ N Y H B K : ℝ, 16 ≤ H → 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N Y H B ξ ≤ K) →
      (∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
        ‖minorCoefficient N Y H B m‖ ^ 2) ^ 2 ≤
        (∫ x in minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2) ^ 2 *
          (∫ x in minorDomain N Y H B, ‖secondSum Y x‖ ^ 2) * K := by
  exact Decomp531a.minor_energy_from_kernel

#print axioms finite_kernel_energy
end
end LeanLab.Languasco2004.Decomp489g
