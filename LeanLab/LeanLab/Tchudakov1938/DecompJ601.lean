/-
AI-written Lean code, Gemini, 2026-10-31, task601.

Decomposition of Lemma 5 from `P0064`.
Represents paper P0064, Lemma 5 on page 30.
-/
import Mathlib
import LeanLab.Tchudakov1938.Tail113
import LeanLab.Tchudakov1938.Deduction

namespace LeanLab.Tchudakov1938.DecompJ601
open Real Finset Filter
open LeanLab.Tchudakov1938.Tail113 (partialSeries)

set_option maxHeartbeats 400000

/-- LEAF. P0064, page 30, Lemma 5 bound on bm via Lemma 2 and Lemma 4. -/
theorem lemma5_bound_bm (M : ℝ) (hM : 0 < M) :
    ∃ c_13 : ℝ, 0 < c_13 ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ n m : ℕ, 6 ≤ n → n ≤ m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_13 * (n : ℝ) / (Real.log n)^2 ≤ ‖(∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))) * partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ := sorry

/-- CITED. P0064, Lemma 5, page 30. -/
def lemma5Statement : Prop :=
  ∀ M : ℝ, 0 < M → ∃ c_13 : ℝ, 0 < c_13 ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ n m : ℕ, 6 ≤ n → n ≤ m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_13 * (n : ℝ) / (Real.log n)^2 ≤ ‖(∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))) * partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖

/-- P0064, Lemma 5, page 30. Assembly theorem for lemma5Statement. -/
theorem lemma5_assembly : lemma5Statement := by
  intro M hM
  exact lemma5_bound_bm M hM

end LeanLab.Tchudakov1938.DecompJ601
