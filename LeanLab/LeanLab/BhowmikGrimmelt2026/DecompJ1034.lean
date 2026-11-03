import LeanLab.BhowmikGrimmelt2026.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace LeanLab.BhowmikGrimmelt2026

-- LEAF 1: Telescoping inequality
/-- LEAF. Page 6. The twin prime constant telescoping lower bound. -/
theorem singular_series_lower_bound (N : ℕ) (hN : Even N) : (1 : ℝ) ≤ singular N := by
  sorry

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
