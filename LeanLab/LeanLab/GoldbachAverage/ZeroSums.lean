import LeanLab.GoldbachAverage.ZeroSumsCore
import LeanLab.GoldbachAverage.LZTheorem1RH
import LeanLab.GoldbachAverage.GYTheorem2RH

/-!
Public theorem wrappers for the previously cited average formulas.
Every original statement is unchanged. The proof imports use ZeroSumsCore.
AI wrote this Lean code. Goldbach is open.
-/

open Finset Complex
noncomputable section
namespace LeanLab.GoldbachAverage

/-- Languasco-Zaccagnini Theorem 1, as in their paper and Goldston-Yang's own Lemma 2:
under RH, `Σ_{n ≤ N} G(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N)`. -/
theorem lz_theorem1 : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 3 := lz_theorem1_proved

/-- Goldston-Yang Theorem 2, their new result: under RH,
`Σ_{n ≤ N} (1 - n/N) G(n) = N²/6 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2)) + O(N)`. -/
theorem gy_theorem2 : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), (1 - (n : ℝ) / N) * G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 6
      + 2 * zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1) * (ρ + 2)))‖ ≤ K * N := gy_theorem2_proved

/-- P0049 Fujii 1991, AS QUOTED in P0052 eq. 1.4 and P0060 Theorem 1: under RH,
`Σ_{n ≤ x} G(n) = x²/2 - 2 Σ_ρ x^{ρ+1}/(ρ(ρ+1)) + O((x log x)^{4/3})`. -/
theorem fujii : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * ((N : ℝ) * Real.log N) ^ ((4 : ℝ) / 3) := fujii_proved

/-- P0050 Bhowmik and Schlage-Puchta 2010, AS QUOTED in P0052 and P0060: under RH the error
`E₂(x)` in Fujii's formula is `O(x log⁵ x)`. -/
theorem bsp_upper : RiemannHypothesis → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N‖
      ≤ K * N * Real.log N ^ 5 := bsp_upper_proved

end LeanLab.GoldbachAverage
