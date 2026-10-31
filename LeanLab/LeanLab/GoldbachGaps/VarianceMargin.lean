/-
P0030 Goldston 1990 page 287, the paragraph before display 11.
A fixed positive gap below the mean square threshold detects an even Goldbach number.
This proves the implication from the stated bound on J. It does not prove that bound.
AI wrote the Lean code. Goldbach is open. Known mathematics.
-/
import LeanLab.GoldbachGaps.Goldston1990Thm6PNT

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter

/-- Every fixed positive variance margin suffices once the window length is large enough. -/
theorem near_even_of_variance_margin (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, B < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Jg N K ≤ (1 - δ) * (K : ℝ) ^ 2 * N →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ Even m ∧ IsGoldbachSum m := by
  obtain ⟨C, hC, hε⟩ := theorem6_proved
  obtain ⟨N0, hN0⟩ := hε (δ / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := eventually_log_small (72 / δ + 6)
  refine ⟨4 * C / δ, by positivity, max (max N0 N1) 3, fun N hN K hKB hKN hJ => ?_⟩
  by_contra hno
  push Not at hno
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hA, hL1, -, hcube⟩ := hN1 N
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_trans (by positivity : (0 : ℝ) < 4 * C / δ) hKB
    exact_mod_cast this
  have hKle := K_le_N hN3 hKN
  have hf := fejer_le_of_noEven hK1 hKle (fun m h1 h2 he hm => hno m h1 h2 he hm)
  have hT := hN0 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) K hK1 hKN
  have hab := neg_abs_le (fejer N K - (K : ℝ) ^ 2 * N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  set L := Real.log N with hL
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2N : Real.log (2 * N) = Real.log 2 + L := Real.log_mul (by norm_num) hNpos.ne'
  have hL3 : L ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have hδL : 72 ≤ δ * L ^ 3 := by
    have h72 : 72 / δ ≤ L := by linarith
    have := (div_le_iff₀ hδ).mp h72
    nlinarith [mul_le_mul_of_nonneg_left hL3 hδ.le]
  have hδN : 72 * (2 * L + 1) ≤ δ * N := by
    calc
      _ ≤ (δ * L ^ 3) * (2 * L + 1) := mul_le_mul_of_nonneg_right hδL (by linarith)
      _ = δ * ((2 * L + 1) * L ^ 3) := by ring
      _ ≤ δ * N := mul_le_mul_of_nonneg_left hcube hδ.le
  have hsmall : 2 * (Real.log 2 * Real.log (2 * N)) ≤ δ * N / 12 := by
    rw [hlog2N]
    have : 2 * (Real.log 2 * (Real.log 2 + L)) ≤ 2 * (1 + L) := by nlinarith
    linarith
  have hodd : fejer N K ≤ δ * (K : ℝ) ^ 2 * N / 4 := by
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 3 * (K : ℝ) ^ 2)
    nlinarith
  have hlast : δ * (K : ℝ) ^ 2 * N / 2 ≤ C * K * N := by linarith
  have hlast' : δ * (K : ℝ) * ((K : ℝ) * N) ≤ (2 * C) * ((K : ℝ) * N) := by nlinarith
  have hcancel := le_of_mul_le_mul_right hlast' (by positivity : (0 : ℝ) < (K : ℝ) * N)
  have hlarge := (div_lt_iff₀ hδ).mp hKB
  nlinarith

/-- The Corollary 3 threshold step after variance error terms have been absorbed.
The displayed variance upper bound remains an explicit premise. -/
theorem near_even_of_corollary3_variance (A ε : ℝ) (hε : 0 < ε) (hgap : 0 < 2 - A - 2 * ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, B < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Real.log N / (2 - A - 2 * ε) < K →
      Jg N K ≤ (A - 1 + ε) * (K : ℝ) ^ 2 * N + K * N * Real.log N →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ Even m ∧ IsGoldbachSum m := by
  obtain ⟨B, hB, N0, hwindow⟩ := near_even_of_variance_margin ε hε
  refine ⟨B, hB, max N0 3, fun N hN K hKB hKN hKlog hJ => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKpos : (0 : ℝ) < K := hB.trans hKB
  apply hwindow N hN0 K hKB hKN
  have hlog : Real.log N < (K : ℝ) * (2 - A - 2 * ε) := (div_lt_iff₀ hgap).mp hKlog
  have hmul := mul_lt_mul_of_pos_left hlog (by positivity : (0 : ℝ) < (K : ℝ) * N)
  nlinarith

end LeanLab.GoldbachGaps.Goldston1990
