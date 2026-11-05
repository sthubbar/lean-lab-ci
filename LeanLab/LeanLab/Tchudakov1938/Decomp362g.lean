/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362g
open Real Filter
set_option maxHeartbeats 400000

/-- LEAF. P0064, page 31, the estimate after display 9. An exponential of a positive logarithmic power dominates any fixed logarithmic power. -/
theorem exp_log_power_tendsto (A b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log x ^ A * Real.exp (-c * Real.log x ^ b)) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / b) c hc).comp
    ((tendsto_rpow_atTop hb).comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp
  have hp : (Real.log x ^ b) ^ (A / b) = Real.log x ^ A := by
    rw [← Real.rpow_mul (Real.log_pos hx).le]
    congr 1
    field_simp
  rw [hp]

/-- LEAF. P0064, page 31, the estimate after display 9. The target scale zeta to power minus two times xi to power minus thirteen sixths equals log x to power minus fifteen halves times M plus six. -/
theorem lemma9_error_scale (M x : ℝ) (hx : 1 < x) :
    ((Real.log x ^ (M + 6)) ^ (8 / 3 : ℝ)) ^ (-2 : ℝ) *
      (Real.log x ^ (M + 6)) ^ (-13 / 6 : ℝ) = Real.log x ^ (-(15 / 2 : ℝ) * (M + 6)) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxi : 0 < Real.log x ^ (M + 6) := Real.rpow_pos_of_pos hlog _
  rw [← Real.rpow_mul hxi.le, ← Real.rpow_add hxi, ← Real.rpow_mul hlog.le]
  congr 1
  ring

/-- P0064, page 31, the estimate after display 9. Both displayed exponential errors are eventually bounded by the target scale. This proves the elementary absorption step, not Lemma 7 or the full Lemma 9. -/
theorem lemma9_error_absorption (M c₁ c₂ K₁ K₂ : ℝ) (hM : 0 < M) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      K₁ * Real.exp (-c₁ * Real.sqrt (Real.log x)) +
        K₂ * Real.exp (-c₂ * Real.log x ^ (1 / (M + 7))) ≤
      ((Real.log x ^ (M + 6)) ^ (8 / 3 : ℝ)) ^ (-2 : ℝ) *
        (Real.log x ^ (M + 6)) ^ (-13 / 6 : ℝ) := by
  let A : ℝ := (15 / 2 : ℝ) * (M + 6)
  have h₁ := exp_log_power_tendsto A (1 / 2) c₁ (by norm_num) hc₁
  have h₂ := exp_log_power_tendsto A (1 / (M + 7)) c₂ (by positivity) hc₂
  have h := (h₁.const_mul K₁).add (h₂.const_mul K₂)
  simp only [mul_zero, add_zero] at h
  have he := h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨X, hX⟩ := eventually_atTop.mp he
  refine ⟨max 3 X, le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) ((le_max_left _ _).trans hx)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hp : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hh := hX x ((le_max_right _ _).trans hx)
  rw [lemma9_error_scale M x hx1]
  have hr : Real.log x ^ (-(15 / 2 : ℝ) * (M + 6)) = (Real.log x ^ A)⁻¹ := by
    rw [show -(15 / 2 : ℝ) * (M + 6) = -A by dsimp [A]; ring, Real.rpow_neg hlog.le]
  rw [hr, ← one_div, le_div_iff₀ hp]
  rw [Real.sqrt_eq_rpow]
  nlinarith

end LeanLab.Tchudakov1938.Decomp362g
