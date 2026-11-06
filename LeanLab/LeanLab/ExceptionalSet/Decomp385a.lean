import LeanLab.ExceptionalSet.Bridge385

/-!
Supply for the sealed DecompJ1140.leaf_small_eps.
Source: https://arxiv.org/abs/2607.27282 pages 9 to 13, display 3.8.
The remaining leaf concerns the weighted mean square, with no exceptional set count.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- LEAF. P0029 page 13 display 3.8, using the zero estimate on page 12 display 3.7.
This is a mean square bound for the weighted error E2 over even indices up to X.
It contains no exceptional set or prime representation assertion.
Only the sublinear epsilon range remains. -/
theorem leaf_mean_square (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The exact sealed small epsilon statement follows from the smaller mean square leaf.
Source: P0029 page 13 after display 3.8, with dyadic summation.
CONDITIONAL ON leaf_mean_square. -/
theorem leaf_small_eps_supplied (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    PowerBound (2 * Θ - 1 / 2 + ε) := by
  by_cases hlinear : 1 ≤ 2 * Θ - 1 / 2 + ε
  · exact powerBound_of_one_le hlinear
  have hsublinear : ε < 3 / 2 - 2 * Θ := by linarith
  apply powerBound_of_even_energy (by linarith : 0 < 2 * Θ - 1 / 2 + ε)
  have hmean := leaf_mean_square Θ hΘ1 hΘ2 hZF ε hε0 hsublinear
  have hexp : 3 / 2 + 2 * Θ + ε = (2 * Θ - 1 / 2 + ε) + 2 := by ring
  simpa only [hexp] using hmean

/-- Theorem 3.1 of P0029 page 9 from the supplied small epsilon statement.
CONDITIONAL ON leaf_mean_square. -/
theorem theorem31_supplied : Theorem31 := by
  intro Θ hΘ1 hΘ2 hZF ε hε
  by_cases hsmall : ε < 1 / 2
  · exact leaf_small_eps_supplied Θ hΘ1 hΘ2 hZF ε hε hsmall
  · apply powerBound_of_one_le
    linarith

end LeanLab.ExceptionalSet.BG2026.Supply385
