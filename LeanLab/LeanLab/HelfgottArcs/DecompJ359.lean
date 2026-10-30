/-
P0013 page 1 to 3 Main Theorem case q ≤ x^{1/3}/6.
AI wrote this Lean code for CODEX task359. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs.DecompJ359
open Real

/-- LEAF. Page 1 equation 1.2 bounds S in terms of some constants. -/
theorem minorArcs_small_leaf (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (hq : (q : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) : ‖S eta2 α x‖ ≤ minorBoundSmall x δ q := by
  sorry

/-- The exact cited small denominator main theorem assembled from the leaf. -/
theorem minorArcs_small_assembled (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) (h : MinorHyp x α a q δ)
    (hq : (q : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) : ‖S eta2 α x‖ ≤ minorBoundSmall x δ q :=
  minorArcs_small_leaf x α a q δ h hq

end LeanLab.HelfgottArcs.DecompJ359
