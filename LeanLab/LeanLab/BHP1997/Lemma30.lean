/-
P0069 Baker, Harman, Pintz 1997, Lemma 30, pages 44 and 45, read from the page images
papers/P0069-original.pdf. Unit U-5094, CLOUD 20261019T0213Z-cloud14.

Exponents of `Y`: `Q = Y^{θ₂/2}`, `qT₂ = Y/Q = Y^{1-θ₂/2}`, `N ≤ Y^{1/2 + θ₂/4 - ε}` (5.5),
`D ≤ γ`, here of size `Y^{ε/2}`, `R = Y/(ND)`.
PROVED: case `j = 0`, `(qT₂ + N²D²)^{1/2} ≤ Y^{1/2-ε/2}Q^{1/2}` and with `(qT₂)^{1/2} = Y^{1/2}/Q^{1/2}`
the product is `Y^{1-ε/2}`; the term `q³/T₂ ≤ qT₂` and `qY²/T₂³ ≤ qT₂` since `q ≤ Q`,
`T₂ = Y/(qQ) ≥ Y^{1-θ₂} ≥ Y^{1/2}`; case `j = 1`, the bracket of (5.7) is the expansion of
`(T + N²D²)(qT + q²/T + R²/T³)` with `N²D²R² = Y²`, and `(qT₂N²D²)^{1/2} ≤ Y^{1-ε/2}`.
FINDING, cosmetic: the display after (5.7) prints `(qTR²D²)^{1/2}` where the bracket has `qTN²D²`;
with `R` the bound fails, at `N = Y^{0.1}`, `D = 1` it is `Y^{1.34}`, `R_version_fails`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma30

/-- Case `j = 0`: `max(1 - θ₂/2, 2n + 2d) ≤ 1 - ε + θ₂/2`, then the product exponent. -/
theorem case0 {th2 ε n d : ℝ} (hε : 0 < ε) (hεθ : ε ≤ th2 / 2) (hn : n ≤ 1 / 2 + th2 / 4 - ε)
    (hd : d ≤ ε / 2) :
    1 - th2 / 2 ≤ 1 - ε + th2 / 2 ∧ 2 * n + 2 * d ≤ 1 - ε + th2 / 2 ∧
      (1 - ε + th2 / 2) / 2 + (1 - th2 / 2) / 2 = 1 - ε / 2 := by
  refine ⟨by linarith, by linarith, by ring⟩

/-- `q³/T₂ ≤ qT₂` and `qY²/T₂³ ≤ qT₂`: in exponents, with `T₂ = 1 - k - θ₂/2` for `q = Y^k`,
`0 ≤ k ≤ θ₂/2`, `θ₂ ≤ 1/2`. -/
theorem case0_terms {k th2 : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ th2 / 2) (hth : th2 ≤ 1 / 2) :
    3 * k - (1 - k - th2 / 2) ≤ k + (1 - k - th2 / 2) ∧
      k + 2 - 3 * (1 - k - th2 / 2) ≤ k + (1 - k - th2 / 2) ∧ 1 / 2 ≤ 1 - k - th2 / 2 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Case `j = 1`: the expansion behind (5.7). -/
theorem eq57_expansion (q T N D R Y : ℝ) (hT : T ≠ 0) (hY : N * D * R = Y) :
    (T + N ^ 2 * D ^ 2) * (q * T + q ^ 2 / T + R ^ 2 / T ^ 3) =
      q * T ^ 2 + q ^ 2 + R ^ 2 / T ^ 2 + q * T * N ^ 2 * D ^ 2 + q ^ 2 * N ^ 2 * D ^ 2 / T +
        Y ^ 2 / T ^ 3 := by
  rw [← hY]; field_simp; ring

/-- `(qT₂N²D²)^{1/2} ≤ Y^{1-ε/2}`, in exponents. -/
theorem N_version {th2 ε n d : ℝ} (hn : n ≤ 1 / 2 + th2 / 4 - ε) (hd : d ≤ ε / 2) :
    ((1 - th2 / 2) + 2 * n + 2 * d) / 2 ≤ 1 - ε / 2 := by linarith

/-- FINDING: with `R = Y/(ND)` the printed term is too big: at `n = 0.1`, `d = 0`, the paper's
`θ₂ = 2(1/16 - 10^-5)`, `((1 - θ₂/2) + 2(1 - n - d))/2 > 1.34 > 1`. -/
theorem R_version_fails :
    let th2 : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    1.34 < ((1 - th2 / 2) + 2 * (1 - 0.1 - 0)) / 2 := by
  intro th2; norm_num [th2]

end LeanLab.BHP1997.Lemma30
