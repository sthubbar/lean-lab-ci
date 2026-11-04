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
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h0 : (0 : ℕ) < N := by
      have h1 : (0 : ℕ) < 2^30 := by norm_num
      omega
    exact_mod_cast h0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := by
      have h2 : (1 : ℕ) ≤ 2^30 := by norm_num
      omega
    exact_mod_cast h1
  -- the exponent `1/2` in the statement is `ℕ`-division, so it is `0`
  have hexp : (N : ℝ) ^ ((1 : ℕ) / 2) = 1 := by norm_num
  rw [hexp, mul_one]
  -- `log N ≤ 6 N^(1/6)`
  have hlog : Real.log (N : ℝ) ≤ 6 * (N : ℝ) ^ ((1:ℝ)/6) := by
    have h := Real.log_le_rpow_div (le_of_lt hNpos) (by norm_num : (0:ℝ) < 1/6)
    calc Real.log (N : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/6) / (1/6) := h
      _ = 6 * (N : ℝ) ^ ((1:ℝ)/6) := by
            rw [div_eq_mul_inv, show ((1:ℝ)/6)⁻¹ = 6 by norm_num, mul_comm]
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  -- so `(log N)^3 ≤ 216 √N`
  have hcube : (Real.log (N : ℝ))^3 ≤ 216 * Real.sqrt (N : ℝ) := by
    have h1 : (Real.log (N : ℝ))^3 ≤ (6 * (N : ℝ) ^ ((1:ℝ)/6))^3 :=
      pow_le_pow_left₀ hlog0 hlog 3
    have h2 : (6 * (N : ℝ) ^ ((1:ℝ)/6))^3 = 216 * Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_pow]
      norm_num
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((1:ℝ)/6)) 3,
        ← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    linarith
  -- and `648 √N ≤ N`
  have hsqrt : (32768 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h : Real.sqrt ((32768:ℝ)^2) ≤ Real.sqrt (N : ℝ) := by
      apply Real.sqrt_le_sqrt
      have : ((32768:ℝ)^2) = ((2:ℕ)^30 : ℝ) := by norm_num
      rw [this]
      exact_mod_cast hN
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 32768)] at h
  have hkey : 648 * Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

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
