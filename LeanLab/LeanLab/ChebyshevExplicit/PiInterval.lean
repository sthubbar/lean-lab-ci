/-
AI wrote the Lean code. Codex task04, 2026-10-22.
Pair the exact Chebyshev lower and upper coefficients.
These statements are derived from local proofs. Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.PiUpperExact

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Retain exact A in the lower pi bound and discard a positive correction. -/
theorem pi_ge_chebyshev30_exact (n : ℕ) (hn : 30 ≤ n) :
    A * n / log n - 5 ≤ (Nat.primeCounting n : ℝ) := by
  have hlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n))
  have hconst : 0 ≤ 2 * log (30 : ℝ) - 1 := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 30)
    linarith [log_two_gt_d9]
  have hp := (psi_ge_chebyshev30 n hn).trans (psi_le_primeCounting_mul_log n)
  rw [sub_le_iff_le_add, div_le_iff₀ hlog]
  nlinarith only [hp, hconst]

/-- A two-sided interval with both exact Chebyshev leading coefficients. -/
theorem pi_chebyshev30_interval (n : ℕ) (hn : 30 ≤ n) (hlog : 32 ≤ log (n : ℝ)) :
    A * n / log n - 5 ≤ (Nat.primeCounting n : ℝ) ∧
      (Nat.primeCounting n : ℝ) ≤ (6 / 5 * A + 5 / log n) * n / log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨pi_ge_chebyshev30_exact n hn, ?_⟩
  simpa only [exp_log hn0, Nat.floor_natCast] using
    pi_exp_le_chebyshev30_add_five_div (log n) hlog

/-- A concrete instance checks that both interval hypotheses hold. -/
theorem pi_chebyshev30_interval_vacuity :
    A * (10 ^ 16 : ℕ) / log (10 ^ 16 : ℕ) - 5 ≤
      (Nat.primeCounting (10 ^ 16) : ℝ) ∧
    (Nat.primeCounting (10 ^ 16) : ℝ) ≤
      (6 / 5 * A + 5 / log (10 ^ 16 : ℕ)) * (10 ^ 16 : ℕ) / log (10 ^ 16 : ℕ) := by
  apply pi_chebyshev30_interval
  · norm_num
  · have h10 : 3 * log (2 : ℝ) ≤ log 10 := by
      have h := log_ge_of_pow 10 3 1 (by norm_num) (by norm_num)
      norm_num at h
      exact h
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_gt_d9]

/-- Every coefficient above exact 6A/5 bounds pi at all sufficiently large naturals. -/
theorem pi_eventually_le_chebyshev30_add_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Nat.primeCounting n : ℝ) ≤ (6 / 5 * A + ε) * n / log n := by
  let T : ℝ := max 32 (5 / ε)
  refine ⟨⌈exp T⌉₊, ?_⟩
  intro n hn
  have hnR : exp T ≤ (n : ℝ) := (Nat.le_ceil (exp T)).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := (exp_pos T).trans_le hnR
  have hlog : max 32 (5 / ε) ≤ log (n : ℝ) :=
    (le_log_iff_exp_le hn0).mpr hnR
  simpa only [exp_log hn0, Nat.floor_natCast] using
    pi_exp_le_chebyshev30_add_epsilon ε (log n) hε hlog

end LeanLab.ChebyshevExplicit
