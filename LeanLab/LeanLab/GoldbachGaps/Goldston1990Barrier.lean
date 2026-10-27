/-
T3 route R-5003, unit U-5034: the mean-square barrier of Goldston 1990, display 10.
Goldston's Theorem detects a sum of two primes near N only through J(N, K) < K² N, up to
lower order terms. Display 10, J(N, h) ≥ (1/2 - ε) h N log N for 1 ≤ h < log^A N, then forbids
that for K ≤ (1/2 - ε) log N: `barrier` below. So no variance method of this shape reaches
windows shorter than about log N; binary Goldbach needs every even N, a window of length 2.
A map entry, not progress on Goldbach, which is open.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main

namespace LeanLab.GoldbachGaps.Goldston1990

/-- Display 10, Goldston 1990 page 287, citing [4]: for `1 ≤ h < log^A N`,
`J(N, h) > (1/2 - ε) h N log N` for large `N`. CITED. -/
def Display10 : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ h : ℕ, 1 ≤ h →
    (h : ℝ) < Real.log N ^ A → (1 / 2 - ε) * h * N * Real.log N < Jg N h

/-- The barrier: once `J(N, K) ≥ c K N log N` and `K ≤ c log N`, the Theorem's sufficient
condition `J(N, K) < K² N` fails. -/
theorem barrier {J K N c L : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N) (hJ : c * K * N * L ≤ J)
    (hKL : K ≤ c * L) : ¬ J < K ^ 2 * N := by
  intro h
  have : K * K * N ≤ c * L * K * N := by
    have := mul_le_mul_of_nonneg_right hKL (mul_nonneg hK hN)
    nlinarith
  nlinarith

/-- Under display 10, for large `N` and `1 ≤ K ≤ (1/2 - ε) log N`, `J(N, K) < K² N` fails. -/
theorem no_detection_below_log (h10 : Display10) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ≤ (1 / 2 - ε) * Real.log N → ¬ Jg N K < (K : ℝ) ^ 2 * N := by
  obtain ⟨N0, hN0⟩ := h10 ε 2 hε two_pos
  refine ⟨max N0 3, fun N hN K hK1 hKL => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have := Real.log_le_log (by norm_num) h3
    have h3e : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_d9]
    linarith
  have hKlt : (K : ℝ) < Real.log N ^ (2 : ℝ) := by
    rw [show Real.log N ^ (2 : ℝ) = Real.log N ^ 2 by norm_cast]
    nlinarith
  have hJ := hN0 N (le_trans (le_max_left _ _) hN) K hK1 hKlt
  exact barrier (Nat.cast_nonneg K) (Nat.cast_nonneg N) hJ.le hKL

end LeanLab.GoldbachGaps.Goldston1990
