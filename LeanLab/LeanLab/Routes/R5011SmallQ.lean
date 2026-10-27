/-
R-5011, T3 MOONSHOT route, CLOUD 20261019T0314Z-cloud15: small-prime Goldbach, every even
`n ≥ 6` is `q + p` with `q` an odd prime at most `C log² n`. The route statement as a Prop and
its link to binary Goldbach. Nothing here is progress on Goldbach; Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Routes.R5011
open Real

/-- The route's unknown statement: every even `n ≥ 6` has an odd prime `q ≤ C log² n` with
`n - q` prime. -/
def SmallPrimeGoldbach (C : ℝ) : Prop :=
  ∀ n : ℕ, Even n → 6 ≤ n → ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ (q : ℝ) ≤ C * log n ^ 2 ∧ (n - q).Prime

/-- Small-prime Goldbach for any `C` implies binary Goldbach. -/
theorem binary_of_smallPrime {C : ℝ} (h : SmallPrimeGoldbach C) : BinaryGoldbach := by
  intro n hn h4
  rcases (show n = 4 ∨ 6 ≤ n by rcases hn with ⟨k, hk⟩; omega) with rfl | h6
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  obtain ⟨q, hq, hq3, -, hp⟩ := h n hn h6
  have hqn : q ≤ n := by
    by_contra hc
    have : n - q = 0 := by omega
    rw [this] at hp; exact Nat.not_prime_zero hp
  exact ⟨q, n - q, hq, hp, by omega⟩

/-- The `n ≥ 6` part is not vacuous and the constant matters: at `n = 6`, `q = 3` works
for any `C ≥ 1`, since `log² 6 > 3`. -/
theorem six_ok {C : ℝ} (hC : 1 ≤ C) : ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ (q : ℝ) ≤ C * log 6 ^ 2 ∧
    (6 - q).Prime := by
  refine ⟨3, Nat.prime_three, le_rfl, ?_, by norm_num⟩
  have h : (1.79 : ℝ) < log 6 := by
    have := Real.add_one_le_exp (0.79 : ℝ)
    have e : Real.exp (1.79 : ℝ) < 6 := by
      have h2 := Real.exp_one_lt_d9
      have : Real.exp (1.79 : ℝ) = Real.exp 1 * Real.exp 0.79 := by rw [← Real.exp_add]; norm_num
      have h79 : Real.exp (0.79 : ℝ) < 2.205 := by
        have hb := Real.exp_bound' (x := (0.79 : ℝ)) (by norm_num) (by norm_num) (n := 10)
          (by norm_num)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
        norm_num at hb; linarith
      rw [this]; nlinarith [Real.exp_pos 1, Real.exp_pos (0.79 : ℝ)]
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact e
  push_cast; nlinarith

end LeanLab.Routes.R5011
