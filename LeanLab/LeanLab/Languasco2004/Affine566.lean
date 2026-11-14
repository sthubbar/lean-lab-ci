/-
Jia 1996 pages 271 to 273, finite endpoint support for the remainder integrals.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderData566
import Mathlib.Analysis.Convex.Jensen

namespace LeanLab.Languasco2004.Affine566
open Real Set RemainderData566
noncomputable section

/-- Pages 271 to 273 support: Mathlib convexity and concavity bound an affine value by its endpoints. -/
theorem affine_bounds (m c a b t : ℝ) (ht : t ∈ Icc a b) :
    min (m * a + c) (m * b + c) ≤ m * t + c ∧
      m * t + c ≤ max (m * a + c) (m * b + c) := by
  have hv := ((LinearMap.mul ℝ ℝ m).convexOn (convex_univ : Convex ℝ (univ : Set ℝ))).add_const c
  have hc := ((LinearMap.mul ℝ ℝ m).concaveOn (convex_univ : Convex ℝ (univ : Set ℝ))).add_const c
  constructor
  · exact hc.min_le_of_mem_Icc (mem_univ a) (mem_univ b) ht
  · exact hv.le_max_of_mem_Icc (mem_univ a) (mem_univ b) ht

/-- Pages 271 to 273 support: all 25 containing rectangles have positive margins. -/
theorem rectangle_certificate : ∀ i : Fin 25,
    0 < data i 0 ∧ data i 0 ≤ data i 1 ∧ 0 < uMin i ∧ uMin i ≤ uMax i ∧
      data i 1 + uMax i < 1 ∧ data i 1 + 2 * uMax i < 1 := by
  decide +kernel

#print axioms affine_bounds
#print axioms rectangle_certificate
end
end LeanLab.Languasco2004.Affine566
