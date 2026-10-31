import LeanLab.LZCesaroShort.Lemma3FirstMoment

/-!
# The remaining analytic input for P0058 Lemma 3

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 3, Lemma 3.
The raw moment is the PNT input displayed in arXiv 1011.3198, page 3.
The two implications below are conditional on that unproved raw moment asymptotic.
The lower order coefficient estimates are unconditional.
-/

namespace LeanLab.LZCesaroShort

open scoped ArithmeticFunction.vonMangoldt

/-- The geometric coefficient contributes at most one plus N over two. -/
theorem geometric_coefficient_le {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, Real.exp (-2 * n / N)) ≤ 1 + (N : ℝ) / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tsum_exp_two_eq hN]
  simpa only [neg_div, one_div_div] using
    (inv_one_sub_exp_neg_le (x := 2 / (N : ℝ)) (by positivity))

/-- Conditional on the raw square moment, all other coefficient terms are lower order. -/
theorem lemma3_moment_of_square_moment (hS : (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N)) - N / 2 * Real.log N| ≤ K * N)) : (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
      - N / 2 * Real.log N| ≤ K * N) := by
  obtain ⟨K, N₀, hK⟩ := hS
  refine ⟨|K| + Real.log 4 + 6, max N₀ 1, fun N hN => ?_⟩
  have hNn : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNn
  have hs := hK N (le_trans (le_max_left _ _) hN)
  have hf := lambda_first_moment_le hNn
  have hg := geometric_coefficient_le hNn
  have hf0 : 0 ≤ ∑' n : ℕ, Λ n * Real.exp (-2 * n / N) :=
    tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  have hg0 : 0 ≤ ∑' n : ℕ, Real.exp (-2 * n / N) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  rw [tsum_exp_two_eq hNn] at hg hg0
  have hKN : K * N ≤ |K| * N :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  rw [lemma3_moment_decomposition hNn, abs_le]
  rw [abs_le] at hs
  constructor <;> nlinarith

/-- The exact Lemma3 Prop is conditional on the raw square moment alone. -/
theorem lemma3_of_square_moment (hS : (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, Λ n ^ 2 * Real.exp (-2 * n / N)) - N / 2 * Real.log N| ≤ K * N)) : Lemma3 :=
  lemma3_of_moment (lemma3_moment_of_square_moment hS)

end LeanLab.LZCesaroShort
