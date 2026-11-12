/-
Identical sealed minor data moved from Decomp413a to avoid an import cycle.
PP1993 pages 43 and 44. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.Decomp413a
open Finset Real MeasureTheory Decomp279b
noncomputable section

/-- Page 44 display 5: the minor part of the chosen integration period. -/
def minorDomain (N Y H B : ℝ) : Set ℝ := period H \ majorSet N Y B

/-- Page 44 display 5: S2 mass in a short interval centred at xi.
The period restriction gives the explicit endpoint version used here. -/
def localMass (N Y H B ξ : ℝ) : ℝ :=
  ∫ α in minorDomain N Y H B ∩ Set.Ioo (ξ - 1 / H) (ξ + 1 / H), ‖secondSum Y α‖ ^ 2

/-- Page 44 display 3: distance to the nearest integer, with the value H
at a kernel pole. This explicit value prevents inverse zero from losing a pole. -/
def kernel (H x : ℝ) : ℝ :=
  if x = (round x : ℤ) then H else min H (|x - (round x : ℤ)|⁻¹)

/-- Page 44 display 3: the squared kernel weighted S2 integral. -/
def kernelMass (N Y H B ξ : ℝ) : ℝ :=
  ∫ α in minorDomain N Y H B, ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2

end
end LeanLab.Languasco2004.Decomp413a
