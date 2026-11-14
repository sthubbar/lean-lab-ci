/-
Jia 1996 pages 271 to 273, exact polynomial integration for source terms 1 to 5.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderKernel566

namespace LeanLab.Languasco2004.NumericRest566a
open Real intervalIntegral RemainderData566 RemainderKernel566 Numeric548 Numeric30_548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Pages 271 to 273: exact polynomial integration certifies five printed components with reserves. -/
theorem block_lower (j : Fin 5) :
    (coefficient ⟨0 + j.val, by omega⟩ : ℝ) + 0.00000001 ≤
      polynomialTerm ⟨0 + j.val, by omega⟩ := by sorry

#print axioms block_lower
end
end LeanLab.Languasco2004.NumericRest566a
