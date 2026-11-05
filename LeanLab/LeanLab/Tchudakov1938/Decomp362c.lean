/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362b
import LeanLab.Tchudakov1938.Triad18

namespace LeanLab.Tchudakov1938.Decomp362c
open Finset
open LeanLab.Tchudakov1938.Tail113

/-- LEAF. P0064, page 28, Lemma 2. Reuse the existing proof in Triad18 with c2 equal to one sixth. -/
theorem weighted_sum_lower (m n : ℕ) (h6 : 6 ≤ n) (hnm : n ≤ m) :
    (1 / 6 : ℝ) * n / Real.log n ^ 2 ≤
      ∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ)) := by
  exact Triad18.triad18_main m n h6 hnm

/-- LEAF. P0064, page 30, Lemma 5 proof display.
Multiply the proved Lemma 2 bound by a positive lower bound for the finite singular series. -/
theorem product_lower (m n Q : ℕ) (h6 : 6 ≤ n) (hnm : n ≤ m)
    (c : ℝ) (hc : 0 < c) (hs : c < ‖partialSeries m Q‖) :
    (c / 6) * (n : ℝ) / (Real.log n)^2 ≤
      ‖(∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))) *
        partialSeries m Q‖ := by
  let S : ℝ := ∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))
  have hS : (1 / 6 : ℝ) * n / Real.log n ^ 2 ≤ S := weighted_sum_lower m n h6 hnm
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  change (c / 6) * (n : ℝ) / (Real.log n)^2 ≤ ‖(S : ℂ) * partialSeries m Q‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS0]
  calc (c / 6) * (n : ℝ) / Real.log n ^ 2 =
      ((1 / 6 : ℝ) * n / Real.log n ^ 2) * c := by ring
    _ ≤ S * ‖partialSeries m Q‖ := mul_le_mul hS hs.le hc.le hS0

/-- CONDITIONAL ON lemma4TruncationStatement. P0064, page 30, Lemma 5.
The full conclusion follows from Lemma 2 and the cited truncation input. -/
theorem lemma5_of_truncation (h : lemma4TruncationStatement) (M : ℝ) (hM : 0 < M) :
    ∃ c_13 : ℝ, 0 < c_13 ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ n m : ℕ, 6 ≤ n → n ≤ m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_13 * (n : ℝ) / (Real.log n)^2 ≤ ‖(∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))) * partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ := by
  obtain ⟨c, hc, X, hX, hb⟩ := h M hM
  exact ⟨c / 6, by positivity, X, hX, fun x hx n m h6 hnm he hdiv =>
    product_lower m n _ h6 hnm c hc (hb x hx m (by omega) he hdiv)⟩

/-- P0064, page 30, Lemma 5. Exact statement of DecompJ601.lemma5_bound_bm.
This assembly depends on the proved divisor leaves in Decomp362b. -/
theorem lemma5_bound_bm (M : ℝ) (hM : 0 < M) :
    ∃ c_13 : ℝ, 0 < c_13 ∧ ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
    ∀ n m : ℕ, 6 ≤ n → n ≤ m → Even m →
      (m.divisors.card : ℝ) ≤ Real.log x ^ (M + 6) / Real.log x →
      c_13 * (n : ℝ) / (Real.log n)^2 ≤ ‖(∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ))) * partialSeries m ⌊Real.log x ^ (M + 6)⌋₊‖ := by
  exact lemma5_of_truncation Decomp362b.partial_sum_bound_lower M hM

end LeanLab.Tchudakov1938.Decomp362c
