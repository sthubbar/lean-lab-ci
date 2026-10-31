/-
AI-written Lean code, Gemini, 2026-10-31, task578.

Decomposition of `lemma4TruncationStatement` from `Tail113.lean`.
Represents paper P0064, Lemma 4 part 4, pages 28 to 30.
-/
import Mathlib
import LeanLab.Tchudakov1938.Tail113

namespace LeanLab.Tchudakov1938.DecompJ578
open Real Finset Filter
open LeanLab.Tchudakov1938.Tail113 (partialSeries lemma4TruncationStatement)

set_option maxHeartbeats 400000

/-- LEAF. P0064, pages 28 to 30.
The partial sum is bounded below by c for sufficiently large x. -/
theorem partial_sum_bound_lower (M : ℝ) (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c < ‖partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ := sorry

/-- P0064, Lemma 4 part 4, pages 28 to 30.
Assembly theorem for lemma4TruncationStatement. -/
theorem lemma4_truncation_assembly : lemma4TruncationStatement := by
  intro M hM
  exact partial_sum_bound_lower M hM

end LeanLab.Tchudakov1938.DecompJ578
