/-
P0014 page 57 Theorem 1.1 Decomposition.
AI wrote this Lean code for CODEX task409. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottArcs.MajorAssembly

namespace LeanLab.HelfgottArcs.DecompJ409
open Real

/-- LEAF. Page 57, the intermediate analytic estimate for Theorem 1.1. -/
theorem major_1_1_leaf (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaHeart χ δ x
      (5.281e-22 + (648662 / √q + 111) / √x + (55 + 1.7e7 / q) / x +
        (19 + 1.2e8 / q) / (x * √x)) := by
  sorry

/-- The exact cited theorem 1.1 assembled from the leaf. -/
theorem major_1_1_assembled (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaHeart χ δ x (5.281e-22 + 1 / √x * (650400 / √q + 112)) :=
  major_1_1_of_error_terms x hx q χ δ (major_1_1_leaf hG x hx q hq χ hχ δ hδ)

end LeanLab.HelfgottArcs.DecompJ409
