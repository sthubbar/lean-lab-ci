/-
P0014 page 57 Theorem 1.2 Decomposition.
AI wrote this Lean code for GEMINI task521. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.HelfgottArcs.MajorAssembly

namespace LeanLab.HelfgottArcs.DecompJ521
open Real

/-- LEAF. Page 57, the intermediate analytic estimate for Theorem 1.2. -/
theorem major_1_2_leaf (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaT2 χ δ x
      (4.269e-14 / q +
        (1.22 * √(1e8 / q) * log (q * (1e8 / q)) + 5.056 * √(1e8 / q) +
          1.423 * log q + 37.19) / √x +
        (3 + 11 * |δ|) / x + (log q + 6) * (1 + 6 * |δ|) / (x * √x)) := by
  sorry

/-- The exact cited theorem 1.2 assembled from the leaf. -/
theorem major_1_2_assembled (hG : HelfgottInput) (x : ℝ) (hx : 10 ^ 8 ≤ x) (q : ℕ) [NeZero q]
    (hq : q ≤ 300000) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ)
    (hδ : |δ| ≤ 4 * 300000 / q) :
    MajorShape etaT2 χ δ x (4.269e-14 / q + 1 / √x * (276600 / √q + 56)) :=
  major_1_2_of_error_terms x hx q hq χ δ hδ (major_1_2_leaf hG x hx q hq χ δ hδ)

end LeanLab.HelfgottArcs.DecompJ521
