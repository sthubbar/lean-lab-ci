/-
P0069 Baker, Harman, Pintz 1997, Lemma 33, page 48, read from the page images
papers/P0069-original.pdf. Unit U-5092, CLOUD 20261019T0213Z-cloud14.

Theorem 4 with `X = Y²`, exponents of `Y`: `M = Y^{β₁}`, `N = Y^{β₂}`, `L = Y^{1-β₁-β₂}`,
`θ = 1/2 + θ₂/4`, `θ₂ = 2(1/16 - 10^-5)`.
PROVED: for `R`, Theorem 4 with `N²L, LM, M` gives `α₁ = (1 + β₂ - β₁)/2`, `α₂ = (1 - β₂)/2`,
`1 - (α₁ + α₂) = β₁/2`, `α₁ - α₂ = (2β₂ - β₁)/2`, `qT₂ = X^{1-θ}`; at this `θ` the binding term of
`γ(θ)` is `(72θ - 37)/11 = (18θ₂ - 1)/11`, so (3.7) is `β₁ < (36θ₂ - 2)/11`, the `c₂` of page 47;
(5.14) holds on `R`, as `2c₁ ≥ c₂ - θ₂`. For `P₁`, `M²N, L², N` give `α₁ = (2β₁ + β₂)/2`,
`α₂ = 1 - β₁ - β₂`, so (3.6) is `|4β₁ + 3β₂ - 2| < θ₂`, (3.7) is `β₂ < c₂`; `P₂` by
`β₁ ↦ 1 - β₁ - β₂` gives `|4β₁ + β₂ - 2|`. All MATCH, up to the paper's `ε` convention.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.BHP1997.Thm4Exponents

namespace LeanLab.BHP1997.Lemma33
open LeanLab.BHP1997.Thm4

theorem R_exponents (b1 b2 : ℝ) :
    (2 * b2 + (1 - b1 - b2)) / 2 = (1 + b2 - b1) / 2 ∧ ((1 - b1 - b2) + b1) / 2 = (1 - b2) / 2 ∧
      1 - ((1 + b2 - b1) / 2 + (1 - b2) / 2) = b1 / 2 ∧
      (1 + b2 - b1) / 2 - (1 - b2) / 2 = (2 * b2 - b1) / 2 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `qT₂ ≍ Y^{1 - θ₂/2} = X^{1-θ}` with `X = Y²`, `θ = 1/2 + θ₂/4`. -/
theorem qT_exponent (th2 : ℝ) : 2 * (1 - (1 / 2 + th2 / 4)) = 1 - th2 / 2 := by ring

/-- At `θ = 1/2 + θ₂/4` with the paper's `θ₂`, `γ(θ) = (72θ - 37)/11 = (18θ₂ - 1)/11`. -/
theorem gam_at :
    gam (1 / 2 + 2 * (1 / 16 - 1 / 10 ^ 5) / 4) = (18 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 1) / 11 := by
  unfold gam
  rw [min_eq_right (by norm_num), min_eq_right (by norm_num)]
  norm_num

/-- (3.7) for `R`: `β₁/2 < (18θ₂ - 1)/11` iff `β₁ < (36θ₂ - 2)/11`, the `c₂` of page 47. -/
theorem R_337 (b1 th2 : ℝ) : b1 / 2 < (18 * th2 - 1) / 11 ↔ b1 < (36 * th2 - 2) / 11 := by
  constructor <;> intro h <;> linarith

/-- (5.14) on `R`: `2β₂ ≥ 2c₁ ≥ c₂ - θ₂ + ε ≥ β₁ - θ₂ + ε` with `c₁ = (1 + 7θ₂)/15 - ε`,
`c₂ = (36θ₂ - 2)/11 - ε`, for the paper's `θ₂` and `ε ≤ 0.02`. -/
theorem R_514 {b1 b2 ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 0.02)
    (hb2 : (1 + 7 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 15 - ε < b2)
    (hb1 : b1 ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) :
    -(2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ 2 * b2 - b1 := by
  norm_num at hb2 hb1 ⊢
  linarith

theorem P1_exponents (b1 b2 : ℝ) :
    (2 * b1 + b2) / 2 - (1 - b1 - b2) = (4 * b1 + 3 * b2 - 2) / 2 ∧
      1 - ((2 * b1 + b2) / 2 + (1 - b1 - b2)) = b2 / 2 := by
  constructor <;> ring

theorem P2_from_P1 (b1 b2 : ℝ) : 4 * (1 - b1 - b2) + 3 * b2 - 2 = -(4 * b1 + b2 - 2) := by ring

end LeanLab.BHP1997.Lemma33
