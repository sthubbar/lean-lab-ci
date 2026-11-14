/-
Jia 1996 pages 271 to 273, ordered reciprocal minorants for numerical support.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Midpoint566

namespace LeanLab.Languasco2004.Midpoint566
open Numeric548 Numeric30_548
noncomputable section

/-- Pages 271 to 273 support: the midpoint reciprocal minorants increase with these three orders. -/
theorem invPoly_chain (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2 * c) :
    invPoly1 x c ≤ invPoly3 x c ∧ invPoly3 x c ≤ invPoly5 x c := by
  have hp := (invPoly1_midpoint x c hx hc hxc).1
  have h3 : invPoly3 x c = invPoly1 x c * (1 + (1 - x / c)^2) := by
    unfold invPoly3 invPoly1
    ring
  have h5 : invPoly5 x c = invPoly1 x c * (1 + (1 - x / c)^2 + (1 - x / c)^4) := by
    unfold invPoly5 invPoly1
    ring
  constructor
  · calc invPoly1 x c = invPoly1 x c * 1 := by ring
         _ ≤ invPoly1 x c * (1 + (1 - x / c)^2) :=
           mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hp
         _ = invPoly3 x c := h3.symm
  · rw [h3, h5]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hp

#print axioms invPoly_chain
end
end LeanLab.Languasco2004.Midpoint566
