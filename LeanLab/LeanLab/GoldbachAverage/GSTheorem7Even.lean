/-
P0051 D. A. Goldston, A. I. Suriajaya, On an average Goldbach representation formula of Fujii,
arXiv 2110.14250v2, Theorem 7, second line, eq. (37), page 7:
`Σ_{n ≤ N, n even} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - 2 N log N + E(N) + O(N)`.
The paper derives it from eq. (13), Theorem 1, and eq. (36), Theorem 7 first line; so does this
file, from the lab's `gs_theorem1_proved` (GSTheorem1.lean) and `gs_theorem7_odd_proved`
(OddSumPNT.lean). Unconditional, no cited input.
Unit U-1350, run PC 20261021T0403Z-14344. AI wrote this Lean code, Claude. Known mathematics.
Binary Goldbach is open; this is an average over n.
-/
import LeanLab.GoldbachAverage.GSTheorem1

open Finset Complex

noncomputable section
namespace LeanLab.GoldbachAverage

/-- The even sum is the full sum minus the odd sum. -/
lemma sum_G_even_eq (N : ℕ) :
    ∑ n ∈ (range (N + 1)).filter Even, G n =
      ∑ n ∈ range (N + 1), G n - ∑ n ∈ (range (N + 1)).filter Odd, G n := by
  rw [← Finset.sum_filter_add_sum_filter_not (range (N + 1)) Even]
  simp only [Nat.not_even_iff_odd]
  ring

/-- **P0051 Theorem 7, second line, eq. (37)**, unconditional: for `N ≥ 2` and `0 < r < 1`,
`Σ_{n ≤ N, n even} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - 2 N log N + E(N) + O(N)`. -/
theorem gs_theorem7_even_proved : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖((∑ n ∈ (range (N + 1)).filter Even, G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N
      + 2 * (N : ℂ) * (Real.log N : ℂ) - EGS N r‖ ≤ K * N := by
  obtain ⟨K1, h1⟩ := gs_theorem1_proved
  obtain ⟨K7, h7⟩ := gs_theorem7_odd_proved
  refine ⟨K1 + K7, fun N hN r hr0 hr1 => ?_⟩
  set A : ℂ := ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r
    with hA
  set B : ℝ := ∑ n ∈ (range (N + 1)).filter Odd, G n - 2 * N * Real.log N with hB
  have key : ((∑ n ∈ (range (N + 1)).filter Even, G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N
      + 2 * (N : ℂ) * (Real.log N : ℂ) - EGS N r = A - (B : ℂ) := by
    rw [hA, hB, sum_G_even_eq]; push_cast; ring
  rw [key]
  have hBn : ‖(B : ℂ)‖ ≤ K7 * N := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact h7 N hN
  calc ‖A - (B : ℂ)‖ ≤ ‖A‖ + ‖(B : ℂ)‖ := norm_sub_le _ _
    _ ≤ K1 * N + K7 * N := add_le_add (h1 N hN r hr0 hr1) hBn
    _ = (K1 + K7) * N := by ring

end LeanLab.GoldbachAverage
