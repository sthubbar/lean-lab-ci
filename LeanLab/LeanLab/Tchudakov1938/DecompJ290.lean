/-
AI-written Lean code, Gemini, 2026-10-28, task290.

Decomposition of `uniformTailStatement` from `Tail113.lean`.
Represents paper P0064, page 29, inequalities (5) through (8).
-/
import Mathlib
import LeanLab.Tchudakov1938.Tail113

namespace LeanLab.Tchudakov1938.DecompJ290
open Real Finset
open LeanLab.Tchudakov1938.Tail113 (tailSeries uniformTailStatement)

set_option maxHeartbeats 400000

/-- LEAF. P0064, page 29, inequalities (5), (6), (7).
The tail sum is bounded by terms c9 and c12 for the split parts s1 and s2. -/
theorem tail_bound_terms :
    ∃ c_9 c_12 : ℝ, 0 < c_9 ∧ 0 < c_12 ∧ ∀ x : ℝ, ∀ m xi : ℕ,
    ‖tailSeries m xi‖ ≤ c_9 * (Real.log (Real.log x))^2 / Real.log x + c_12 * (Real.log (Real.log x))^2 / Real.log x := sorry

/-- LEAF. P0064, page 29, inequality (8).
Combining the bounds for the split terms gives the required limit for sufficiently large x. -/
theorem tail_bound_combined (M : ℝ) (hM : 0 < M) (c_9 c_12 : ℝ) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ m : ℕ, 0 < m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_9 * (Real.log (Real.log x))^2 / Real.log x + c_12 * (Real.log (Real.log x))^2 / Real.log x ≤ (1 / 4 : ℝ) := sorry

theorem uniform_tail_assembly : uniformTailStatement := by
  intro M hM
  have ⟨c_9, c_12, hc9, hc12, hbound⟩ := tail_bound_terms
  obtain ⟨X₀, hX₀, hcomb⟩ := tail_bound_combined M hM c_9 c_12
  exact ⟨X₀, hX₀, fun x hx m hm heven hdiv => le_trans (hbound x m ⌊Real.log x ^ (M + 6)⌋₊) (hcomb x hx m hm heven hdiv)⟩

end LeanLab.Tchudakov1938.DecompJ290
