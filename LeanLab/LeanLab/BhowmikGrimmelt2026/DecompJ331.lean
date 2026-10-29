import Mathlib
import LeanLab.BhowmikGrimmelt2026.Statements

open Filter Topology Real

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF p. 22: `H^A > X^{A-2}` iff `θ > 1 - 2/A`.
This was already proved as `thm62_iff`. -/
theorem leaf_thm62_iff (A X H θ : ℝ) (hA : 0 < A) (hX : 1 < X) (hH : H = X ^ θ) :
    X ^ (A - 2) < H ^ A ↔ 1 - 2 / A < θ := by
  rw [hH, ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hX)), Real.rpow_lt_rpow_left_iff hX]
  constructor
  · intro h
    have h1 : (A - 2) / A < (θ * A) / A := (div_lt_div_iff_of_pos_right hA).mpr h
    rw [mul_div_cancel_right₀ θ (ne_of_gt hA)] at h1
    have h2 : (A - 2) / A = 1 - 2 / A := by
      rw [sub_div, div_self (ne_of_gt hA)]
    rwa [h2] at h1
  · intro h
    have h1 : (1 - 2 / A) * A < θ * A := (mul_lt_mul_of_pos_right h hA)
    have h2 : (1 - 2 / A) * A = A - 2 := by
      rw [sub_mul, one_mul, div_mul_cancel₀ 2 (ne_of_gt hA)]
    rwa [h2] at h1

/-- LEAF p. 22: Given `N(σ,T) ≪ T^{A(1-σ)}(log T)^B`, the off-diagonal integral is bounded. -/
theorem leaf_off_diagonal_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hDensity : ∃ C : ℝ, ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaN σ T : ℝ) ≤ C * T ^ (A * (1 - σ)) * Real.log T ^ B)
    (θ : ℝ) (hθ : 1 - 2 / A < θ) :
    Tendsto (fun X : ℝ => V X (X ^ θ) / ((X ^ θ) ^ 2 * X)) atTop (𝓝 0) := by
  sorry

/-- Theorem 6.2 decomposed. -/
theorem decomp_theorem62 : Theorem62 := by
  intro A B hA hB hDensity θ hθ
  exact leaf_off_diagonal_bound A B hA hB hDensity θ hθ

end LeanLab.BhowmikGrimmelt2026
