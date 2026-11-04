import LeanLab.BhowmikGrimmelt2026.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace LeanLab.BhowmikGrimmelt2026

-- LEAF 1: Telescoping inequality
/-- LEAF. Page 6. The twin prime constant telescoping lower bound. -/
theorem singular_series_lower_bound (N : ℕ) (hN : Even N) : (1 : ℝ) ≤ singular N := by
  unfold singular
  have hq1 : (((moebius 1 : ℤ) : ℝ) ^ 2 / (Nat.totient 1 : ℝ) ^ 2) * (ramanujan 1 N).re = 1 := by
    simp [ramanujan]
  -- The q=1 term is exactly 1. We need to show the remaining sum is nonnegative.
  -- Use the identity: singular N = 2 * ∏_{p | N, p > 2} (p-1)/(p-2)
  -- This is a standard result; we'll prove it via the Euler product.
  -- For now, use a direct bound: the singular series is known to be ≥ 1 for even N.
  -- We'll prove this by showing the q=1 term dominates.
  have h_nonneg_tail : 0 ≤ ∑' q : ℕ, (((moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) * (ramanujan q N).re - 1 := by
    -- This is the tail sum starting from q=2
    -- We need to show this is nonnegative
    -- This is a known result: the singular series tail is nonnegative for even N
    sorry
  linarith

-- LEAF 2: von Mangoldt factor upper bound for Goldbach exceptions
/-- LEAF. Page 13. Proper prime power sum bound. -/
theorem r2_prime_power_bound (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
  r2 N ≤ 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 := by
  sorry

-- LEAF 3: Asymptotic inequality
/-- LEAF. Page 13. Size comparison for large N. -/
theorem r2_bound_le_half_N (N : ℕ) (hN : 2^30 ≤ N) :
  3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 ≤ 1/2 * N := by
  sorry

theorem exceptional_gap150 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ¬ IsGoldbachSum N → c * N ≤ |E2 N| := by
  use 1 / 2
  refine ⟨by norm_num, 2^30, ?_⟩
  intro N hN hEven hNotG
  have h1 : 1 ≤ singular N := singular_series_lower_bound N hEven
  have h2 : r2 N ≤ 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 := r2_prime_power_bound N hEven hNotG
  have h3 : 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 ≤ 1/2 * N := r2_bound_le_half_N N hN
  have h4 : r2 N ≤ 1/2 * N := le_trans h2 h3
  unfold E2
  have h5 : (N : ℝ) * singular N ≥ N := by
    calc (N : ℝ) * singular N ≥ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
         _ = N := mul_one _
  have h6 : (N : ℝ) * singular N - r2 N ≥ 1/2 * N := by
    linarith
  rw [abs_sub_comm]
  exact le_trans h6 (le_abs_self _)

end LeanLab.BhowmikGrimmelt2026
