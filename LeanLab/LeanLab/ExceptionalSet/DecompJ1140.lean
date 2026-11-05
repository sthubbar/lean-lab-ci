import Mathlib
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

namespace LeanLab.ExceptionalSet.BG2026

open Real Finset ArithmeticFunction

/-- LEAF 1: Theorem 3.1 for large epsilon. -/
theorem leaf_large_eps (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (_hΘ2 : Θ < 3 / 4) (_hZF : ZeroFreeBeyond Θ)
    (ε : ℝ) (hε : 1 / 2 ≤ ε) : PowerBound (2 * Θ - 1 / 2 + ε) := by
  refine ⟨1, fun X hX => ?_⟩
  have hE : (E X : ℝ) ≤ X := by exact_mod_cast E_le X
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (1 : ℝ) ≤ 2 * Θ - 1 / 2 + ε := by linarith
  have h2 : (X : ℝ) ≤ (X : ℝ) ^ (2 * Θ - 1 / 2 + ε) := by
    have h3 := Real.rpow_le_rpow_of_exponent_le hX1 hpow
    rwa [Real.rpow_one] at h3
  calc (E X : ℝ) ≤ (X : ℝ) := hE
    _ = 1 * (X : ℝ) := by ring
    _ ≤ 1 * (X : ℝ) ^ (2 * Θ - 1 / 2 + ε) := by gcongr

/-- LEAF 2: Theorem 3.1 for small epsilon. -/
theorem leaf_small_eps (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4) (hZF : ZeroFreeBeyond Θ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) : PowerBound (2 * Θ - 1 / 2 + ε) := by
  sorry

/-- Assembly. -/
theorem theorem31_assembly : Theorem31 := by
  intro Θ hΘ1 hΘ2 hZF ε hε0
  by_cases hε : 1 / 2 ≤ ε
  · exact leaf_large_eps Θ hΘ1 hΘ2 hZF ε hε
  · push Not at hε
    exact leaf_small_eps Θ hΘ1 hΘ2 hZF ε hε0 hε

end LeanLab.ExceptionalSet.BG2026
