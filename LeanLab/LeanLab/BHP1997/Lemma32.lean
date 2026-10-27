/-
P0069 Baker, Harman, Pintz 1997, Lemma 32, pages 46 and 47, read from the page images
papers/P0069-original.pdf. Unit U-5091, CLOUD 20261019T0213Z-cloud14.

`β = 2(h + α)`, `τ = 2β/(β - 2) = 2(h + α)/(h - 1 + α)`, `h ≥ 1`, `α > 0`.
PROVED: `tau_eq`; `holder`, `1/β + 1/τ = 1/2`, the exponents of (5.10); `key_identity`,
`1/(1 - φ) - 4/(2 + τ) = φ/(1 - φ) + 1/(2h - 1 + 2α)`, the display on page 47, so (5.9) gives
`M^{2+τ} ≥ (qTY^ε)⁴`, `M_exponent`; `lemma2_M`, Lemma 2 for `M` with `τ, 1, (τ+2)/4 - ε` satisfies
(3.18) with room `3ε`; `lemma2_N`, for `N` with `γ = 1/(λ + ε)`, `β - 4γ + 2h = 4h + 2α - 4/(λ+ε)`
and this is at least `4/λ - 4/(λ + ε) > 0` when `λ ≥ 2/(2h + α)`. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma32

theorem tau_eq {h α : ℝ} (hh : 1 ≤ h) (hα : 0 < α) :
    2 * (2 * (h + α)) / (2 * (h + α) - 2) = 2 * (h + α) / (h - 1 + α) := by
  have h1 : h - 1 + α ≠ 0 := by linarith
  have h2 : 2 * (h + α) - 2 ≠ 0 := by linarith
  rw [div_eq_div_iff h2 h1]; ring

theorem holder {h α : ℝ} (hh : 1 ≤ h) (hα : 0 < α) :
    1 / (2 * (h + α)) + 1 / (2 * (h + α) / (h - 1 + α)) = 1 / 2 := by
  have h1 : h - 1 + α ≠ 0 := by linarith
  have h2 : h + α ≠ 0 := by linarith
  field_simp; ring

theorem key_identity {h α φ : ℝ} (hh : 1 ≤ h) (hα : 0 < α) (hφ : φ < 1) :
    1 / (1 - φ) - 4 / (2 + 2 * (h + α) / (h - 1 + α)) = φ / (1 - φ) + 1 / (2 * h - 1 + 2 * α) := by
  have h1 : h - 1 + α ≠ 0 := by linarith
  have h2 : 2 * h - 1 + 2 * α ≠ 0 := by linarith
  have h3 : 1 - φ ≠ 0 := by linarith
  have h4 : 2 + 2 * (h + α) / (h - 1 + α) = 2 * (2 * h - 1 + 2 * α) / (h - 1 + α) := by
    field_simp; ring
  rw [h4]
  field_simp; ring

/-- With `Y = (qTY^ε)^{1/(1-φ)}`, `N = (qTY^ε)^λ`, `M = Y/N`, the exponent of `M` in units of
`log(qTY^ε)` is `1/(1-φ) - λ`, and (5.9)'s upper bound gives `(2 + τ)(1/(1-φ) - λ) ≥ 4`. -/
theorem M_exponent {h α φ lam : ℝ} (hh : 1 ≤ h) (hα : 0 < α) (hφ : φ < 1)
    (h59 : lam ≤ φ / (1 - φ) + 1 / (2 * h - 1 + 2 * α)) :
    4 ≤ (2 + 2 * (h + α) / (h - 1 + α)) * (1 / (1 - φ) - lam) := by
  have hpos : 0 < 2 + 2 * (h + α) / (h - 1 + α) := by
    have : 0 < h - 1 + α := by linarith
    positivity
  have hk := key_identity hh hα hφ
  have : 4 / (2 + 2 * (h + α) / (h - 1 + α)) ≤ 1 / (1 - φ) - lam := by linarith
  rw [div_le_iff₀ hpos] at this
  linarith

/-- Lemma 2 for `M` with `β, h, γ` replaced by `τ, 1, (τ + 2)/4 - ε`: (3.18) `τ ≥ 4γ - 2 + ε`. -/
theorem lemma2_M (τ ε : ℝ) (hε : 0 < ε) : 4 * ((τ + 2) / 4 - ε) - 2 * 1 + ε ≤ τ := by linarith

/-- Lemma 2 for `N`, `γ = 1/(λ + ε)`: `β - 4γ + 2h = 4h + 2α - 4/(λ + ε) ≥ 4/λ - 4/(λ + ε) > 0`. -/
theorem lemma2_N {h α lam ε : ℝ} (hl : 0 < lam) (hε : 0 < ε) (h59 : 2 / (2 * h + α) ≤ lam)
    (hh : 0 < 2 * h + α) :
    2 * (h + α) - 4 / (lam + ε) + 2 * h = 4 * h + 2 * α - 4 / (lam + ε) ∧
      4 / lam - 4 / (lam + ε) ≤ 4 * h + 2 * α - 4 / (lam + ε) ∧ 0 < 4 / lam - 4 / (lam + ε) := by
  refine ⟨by ring, ?_, ?_⟩
  · have : 4 / lam ≤ 4 * h + 2 * α := by
      rw [div_le_iff₀ hl]
      rw [div_le_iff₀ hh] at h59
      nlinarith
    linarith
  · have : 4 / (lam + ε) < 4 / lam := div_lt_div_of_pos_left (by norm_num) hl (by linarith)
    linarith

end LeanLab.BHP1997.Lemma32
