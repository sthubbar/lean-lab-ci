import LeanLab.LZCesaroShort.Lemma13Statements
import LeanLab.LZCesaroShort.Lemma3Parseval
import LeanLab.LZCesaroShort.Lemma3Reduction

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

/-- LEAF arXiv:1606.00869v2 page 3, using PNT. Bound the sum using Prime Number Theorem. -/
theorem lemma3_raw_moment_asymptotic : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N)) - N / 2 * Real.log N| ≤ K * N := by sorry

/-- LEAF arXiv:1606.00869v2 page 3, Parseval step bounds -/
theorem lemma3_parseval_bound : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
      - N / 2 * Real.log N| ≤ K * N := by sorry

/-- LEAF arXiv:1606.00869v2 page 3, Parseval step exact moment -/
theorem lemma3_parseval_exact_moment : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2) - N / 2 * Real.log N|
      ≤ K * N * Real.sqrt (Real.log N) := by sorry

/-- The exact Lemma3 Prop is conditional on the raw square moment alone. -/
theorem lz_lemma3_decomp_assembly : Lemma3 :=
  lemma3_of_square_moment lemma3_raw_moment_asymptotic

end LeanLab.LZCesaroShort
