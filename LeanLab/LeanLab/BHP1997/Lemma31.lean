/-
P0069 Baker, Harman, Pintz 1997, Lemma 31, page 46, read from the page images
papers/P0069-original.pdf. Unit U-5090, CLOUD 20261019T0213Z-cloud14.

PROVED: `case2`, the "straightforward calculation" `2/(2h + α) ≤ 1/(2h + 1) + 1/(2h - 1 + 2α)` for
`h ≥ 1`, `0 ≤ α ≤ 1`: cleared of denominators the difference is exactly `2(1 - α)²`, `case2_identity`;
`phi_ratio`, `1/(2j + 2) < φ ≤ 1/(2j)` gives `1/(2j + 1) < φ/(1 - φ) ≤ 1/(2j - 1)`; and `h_ge_j`, a
`λ ≤ 1/(2j-1) + 1/(2j-1+2ε) < 2/(2j - 1)` lies in no interval `(2/(2h + ε), 2/(2h - 1)]` with
`h < j`, so `h ≥ j` in Cases 1 and 2. MATCH. The printed lower bound
`2/(2j+1) - 1/(2j+1+ε) ≤ φ/(1-φ)` holds once `ε` is small for the fixed `φ > 1/(2j+2)`, the
paper's convention, and is not used.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma31

theorem case2_identity (h α : ℝ) :
    (2 * h + α) * ((2 * h - 1 + 2 * α) + (2 * h + 1)) - 2 * ((2 * h + 1) * (2 * h - 1 + 2 * α)) =
      2 * (1 - α) ^ 2 := by ring

theorem case2 {h α : ℝ} (hh : 1 ≤ h) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    2 / (2 * h + α) ≤ 1 / (2 * h + 1) + 1 / (2 * h - 1 + 2 * α) := by
  have h1 : 0 < 2 * h + α := by linarith
  have h2 : 0 < 2 * h + 1 := by linarith
  have h3 : 0 < 2 * h - 1 + 2 * α := by linarith
  rw [div_add_div _ _ h2.ne' h3.ne', div_le_div_iff₀ h1 (mul_pos h2 h3)]
  nlinarith [case2_identity h α, sq_nonneg (1 - α)]

theorem phi_ratio {j φ : ℝ} (hj : 1 ≤ j) (h1 : 1 / (2 * j + 2) < φ) (h2 : φ ≤ 1 / (2 * j)) :
    1 / (2 * j + 1) < φ / (1 - φ) ∧ φ / (1 - φ) ≤ 1 / (2 * j - 1) := by
  have hj2 : 0 < 2 * j := by linarith
  have hφ1 : φ < 1 := by
    have : 1 / (2 * j) ≤ 1 / 2 := by rw [div_le_div_iff₀ hj2 (by norm_num)]; linarith
    linarith
  have hφ0 : 0 < φ := lt_trans (by positivity) h1
  have h1' : 1 < φ * (2 * j + 2) := by rwa [div_lt_iff₀ (by linarith)] at h1
  have h2' : φ * (2 * j) ≤ 1 := by rwa [le_div_iff₀ hj2] at h2
  constructor
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem h_ge_j {j h ε lam : ℝ} (hj : 1 ≤ j) (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : 1 ≤ h)
    (hl : lam ≤ 1 / (2 * j - 1) + 1 / (2 * j - 1 + 2 * ε)) (hlow : 2 / (2 * h + ε) < lam)
    (hhj : h ≤ j - 1) : False := by
  have hA : 0 < 2 * j - 1 := by linarith
  have h1 : 1 / (2 * j - 1 + 2 * ε) < 1 / (2 * j - 1) :=
    one_div_lt_one_div_of_lt hA (by linarith)
  have h2 : 2 / (2 * j - 1) ≤ 2 / (2 * h + ε) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have : 1 / (2 * j - 1) + 1 / (2 * j - 1) = 2 / (2 * j - 1) := by ring
  linarith

end LeanLab.BHP1997.Lemma31
