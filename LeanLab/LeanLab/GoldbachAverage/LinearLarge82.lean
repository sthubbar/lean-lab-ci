import LeanLab.GoldbachAverage.OddSumPNT

/-!
A weaker large count consequence of the unconditional average estimates.
Source context: P0050 arXiv 0806.3295v3 pages 4 and 5.
This bound lacks the log log factor required by the omega argument.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.LinearLarge82
open Finset Filter

/-- The unconditional PNT gives psi of N at least N over two eventually.
Source: the elementary average comparison used before the large count argument. -/
theorem psi_half_eventually : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 2 ≤ psiN N := by
  obtain ⟨A, hA, hb⟩ := psi_div_log
  have ht : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (2 * A + 1))
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog := hN₀ N (le_trans (le_max_left _ _) hN)
  have hlog0 : 0 < Real.log N := by linarith
  have hpsi := hb N hNr
  have he : A * (N : ℝ) / Real.log N ≤ (N : ℝ) / 2 := by
    rw [div_le_iff₀ hlog0]
    have hm := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg N)
    nlinarith
  rw [psiN_eq]
  have hl := (abs_le.mp hpsi).1
  linarith

/-- The elementary average route gives arbitrarily large G of N at least N over 32.
This is weaker than the n log log n count required in P0050 pages 4 and 5. -/
theorem large_G_linear : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ (1 / 32 : ℝ) * N ≤ G N := by
  intro N₀
  obtain ⟨N₁, h₁⟩ := psi_half_eventually
  set S := ∑ n ∈ range N₀, G n with hSdef
  have hS : 0 ≤ S := sum_nonneg (fun n _ => G_nonneg n)
  let M : ℕ := max N₁ ⌈16 * (S + 1)⌉₊ + 2
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hM0 : (0 : ℝ) < M := by linarith
  have hMS : 16 * (S + 1) ≤ (M : ℝ) := by
    have hc := Nat.le_ceil (16 * (S + 1))
    have hle : ⌈16 * (S + 1)⌉₊ ≤ M := by dsimp [M]; omega
    exact hc.trans (by exact_mod_cast hle)
  have hp := h₁ M (by dsimp [M]; omega)
  have hp0 : 0 ≤ psiN M := by rw [psiN_eq]; exact Chebyshev.psi_nonneg _
  have hsum := sum_G_ge M
  have hlower : (M : ℝ) ^ 2 / 4 ≤ ∑ n ∈ range (2 * M + 1), G n := by
    have hsq : (M : ℝ) ^ 2 / 4 ≤ psiN M ^ 2 := by nlinarith
    exact hsq.trans hsum
  have hex : ∃ n ∈ range (2 * M + 1), (M : ℝ) / 16 ≤ G n := by
    by_contra! hn
    have hu := sum_lt_sum (fun n hn' => (hn n hn').le)
      (show ∃ n ∈ range (2 * M + 1), G n < (M : ℝ) / 16 from
        ⟨0, by simp, hn 0 (by simp)⟩)
    simp only [sum_const, card_range, nsmul_eq_mul] at hu
    push_cast at hu
    nlinarith
  obtain ⟨n, hn, hGn⟩ := hex
  have hnM : n ≤ 2 * M := by simpa only [mem_range, Nat.lt_succ_iff] using hn
  have hn₀ : N₀ ≤ n := by
    by_contra hn₀
    have hnS : G n ≤ S := by
      apply single_le_sum (fun j _ => G_nonneg j)
      exact mem_range.mpr (by omega)
    linarith
  refine ⟨n, hn₀, ?_⟩
  have hnm : (n : ℝ) ≤ 2 * M := by exact_mod_cast hnM
  linarith

end LeanLab.GoldbachAverage.LinearLarge82
