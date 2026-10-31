/-
P0075 Chirre-Hagen 2025, end of Section 4: the step from (4.4), (4.7), (4.9) to Theorem 3's
constant 2.5571 with η = 0.0693. The paper keeps the term (1 + 1/η)² δ² x² / 2 outside its
bracket and does not say it is absorbed; this module checks that it is, for δ ≤ 10^-13.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ChirreHagen2025
open Real

theorem log_2e13_ge : 30.625 ≤ Real.log (2.0001 * 10 ^ 13) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h8 : Real.exp 30.625 ^ 8 = Real.exp 1 ^ 245 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have hb : Real.exp 1 ^ 245 ≤ (2.7182818286 : ℝ) ^ 245 := by
    gcongr; exact Real.exp_one_lt_d9.le
  have : Real.exp 30.625 ^ 8 ≤ (2.0001 * 10 ^ 13 : ℝ) ^ 8 := by
    rw [h8]; refine le_trans hb ?_; norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this

/-- Section 4, final step: with `η = 0.0693`, `ℓ < 2.0001`, `0 < δ ≤ 10^-13`, the bound
(4.4) with (4.7) and (4.9) inserted gives `J ≤ 2.5571 δ log²(2.0001/δ) x²`. -/
theorem step6 (J x δ ℓ : ℝ) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13) (hℓ : 0 ≤ ℓ) (hℓ2 : ℓ < 2.0001)
    (h : J ≤ (1 + 0.0693) * 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2
      + (1 + 1 / 0.0693) ^ 2 * δ ^ 2 * x ^ 2 / 2
      + 15.8052 * (1 + 0.0693) ^ 2 * ℓ * δ * x ^ 2 / (0.0693 * π)) :
    J ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 := by
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 30.625 ≤ u := by
    refine le_trans log_2e13_ge (Real.log_le_log (by norm_num) ?_)
    rw [le_div_iff₀ hδ]
    calc 2.0001 * 10 ^ 13 * δ ≤ 2.0001 * 10 ^ 13 * (1 / 10 ^ 13) := by gcongr
      _ = 2.0001 := by norm_num
  have hpi : 3.1415 < π := Real.pi_gt_d4
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hu2 : 937.890625 ≤ u ^ 2 := by nlinarith
  -- the ℓ term
  have t3 : 15.8052 * (1 + 0.0693) ^ 2 * ℓ * δ * x ^ 2 / (0.0693 * π)
      ≤ 166.03 * δ * x ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 15.8052 * (1 + 0.0693) ^ 2 * ℓ ≤ 15.8052 * (1 + 0.0693) ^ 2 * 2.0001 := by
      gcongr
    have hD : 0 ≤ δ * x ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hD]
  -- the δ² term
  have t2 : (1 + 1 / 0.0693) ^ 2 * δ ^ 2 * x ^ 2 / 2 ≤ 120 * (1 / 10 ^ 13) * δ * x ^ 2 := by
    have : (1 + 1 / 0.0693 : ℝ) ^ 2 / 2 ≤ 120 := by norm_num
    have hD : 0 ≤ δ * x ^ 2 := by positivity
    calc (1 + 1 / 0.0693) ^ 2 * δ ^ 2 * x ^ 2 / 2 = ((1 + 1 / 0.0693 : ℝ) ^ 2 / 2) * δ * (δ * x ^ 2) := by ring
      _ ≤ 120 * (1 / 10 ^ 13) * (δ * x ^ 2) := by gcongr
      _ = 120 * (1 / 10 ^ 13) * δ * x ^ 2 := by ring
  -- combine, using δ x² ≤ δ u² x² / 937.89
  have hD : 0 ≤ δ * x ^ 2 := by positivity
  have key : (166.03 + 120 * (1 / 10 ^ 13)) * (δ * x ^ 2)
      ≤ (2.5571 - (1 + 0.0693) * 2.2258) * (δ * u ^ 2 * x ^ 2) := by
    have : (166.03 + 120 * (1 / 10 ^ 13) : ℝ) ≤ (2.5571 - (1 + 0.0693) * 2.2258) * 937.890625 := by
      norm_num
    have e : δ * u ^ 2 * x ^ 2 = u ^ 2 * (δ * x ^ 2) := by ring
    rw [e]
    calc (166.03 + 120 * (1 / 10 ^ 13)) * (δ * x ^ 2)
        ≤ ((2.5571 - (1 + 0.0693) * 2.2258) * 937.890625) * (δ * x ^ 2) := by gcongr
      _ ≤ (2.5571 - (1 + 0.0693) * 2.2258) * (u ^ 2 * (δ * x ^ 2)) := by
        rw [mul_assoc]; gcongr
  nlinarith

end LeanLab.ChirreHagen2025
