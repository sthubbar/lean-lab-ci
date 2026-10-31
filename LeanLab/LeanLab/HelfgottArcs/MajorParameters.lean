/-
Height choices for Helfgott's major arcs.
Source: https://arxiv.org/abs/1305.2897v4, pages 56 to 59, equation 4.86.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open Real

/-- The Gaussian height is large enough and its ratio covers every nonzero delta. -/
theorem gaussian_height_bounds {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 1200000 / q) :
    1000 / 3 ≤ 1e8 / q ∧ 4 * π ^ 2 * |δ| ≤ 1e8 / q ∧
      (δ = 0 ∨ 1000 / (12 * π) ≤ (1e8 / q) / (π * |δ|)) := by
  have hq0 : 0 < q := by linarith
  have hdq : |δ| * q ≤ 1200000 := (le_div_iff₀ hq0).mp hδ
  have hp0 : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq0]
    nlinarith
  · rw [le_div_iff₀ hq0]
    have hmul := mul_le_mul_of_nonneg_left hdq (show 0 ≤ 4 * π ^ 2 by positivity)
    have hp := Real.pi_lt_four
    nlinarith [sq_nonneg π]
  · by_cases hz : δ = 0
    · exact Or.inl hz
    · right
      have hd0 : 0 < |δ| := abs_pos.mpr hz
      rw [le_div_iff₀ (mul_pos hp0 hd0), div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity : 0 < 12 * π) hq0]
      nlinarith [mul_le_mul_of_nonneg_left hdq hp0.le]

/-- The etaPlus height is covered by Helfgott's odd and even verification ranges. -/
theorem etaPlus_height_within_verification (q : ℕ) [NeZero q]
    (hq : (¬ Even q ∧ q ≤ 150000) ∨ (Even q ∧ q ≤ 300000)) :
    200 + 250 * (if Even q then (300000 : ℝ) else 150000) / q ≤
      if Even q then max (1e8 / (q : ℝ)) (200 + 7.5e7 / q) else 1e8 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rcases hq with ⟨hodd, hq⟩ | ⟨heven, hq⟩
  · simp only [if_neg hodd]
    have hqr : (q : ℝ) ≤ 150000 := by exact_mod_cast hq
    rw [le_div_iff₀ hq0]
    have hh : (250 * 150000 / (q : ℝ)) * q = 250 * 150000 := div_mul_cancel₀ _ hq0.ne'
    nlinarith
  · simp only [if_pos heven]
    refine le_trans ?_ (le_max_right _ _)
    norm_num

/-- The optimized q = 1 height stays inside the verification and meets the decay thresholds. -/
theorem etaPlus_q1_height_bounds {δ : ℝ} (hδ : |δ| ≤ 600000) :
    1.2e7 * π + 200 < 1e8 ∧
      200 + 4 * π ^ 2 * |δ| ≤ 1.2e7 * π + 200 ∧
      (δ = 0 ∨ 20 ≤ (1.2e7 * π) / (π * |δ|)) := by
  have hp := Real.pi_lt_four
  have hp0 := Real.pi_pos
  refine ⟨by linarith, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 4 * π ^ 2 by positivity)
    have hsq : π ^ 2 < 4 * π := by nlinarith
    nlinarith
  · by_cases hz : δ = 0
    · exact Or.inl hz
    · right
      rw [le_div_iff₀ (mul_pos hp0 (abs_pos.mpr hz))]
      have hmul := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 20 * π by positivity)
      nlinarith

end LeanLab.HelfgottArcs
