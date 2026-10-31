/-
P0069 Baker, Harman, Pintz 1997, Lemmas 15 and 16, pages 30 and 31, read from the page images
papers/P0069-original.pdf. Unit U-5082, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`: `μ, ν` for `M, N`, `π` for `p`, `ζ` for `z`.
PROVED, every exponent step: Lemma 15, `pm > x^{0.46}` with `M ≤ N ≤ x^{0.4}`, `p < x^{0.1}`
gives `h ≤ x^{0.18}`, `mp/n ≤ p < x^{0.1}` and `n/mp < 1`. Lemma 16, the induction step: in `t_k`,
`mp < x^{(α+2)/10} ≤ x^{0.5}` for `α ≤ 3`, attained at the top of the `M` range; `β ≥ α + 1`;
and then both hypotheses of (4.23) at level `β` follow, `p^{9-2β} ≤ x^{1.1}/(M²p²)` and
`MpN ≤ x^{0.775} p^{β-4}`, exactly as the page says. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma1516

/-- Lemma 15, `pm > x^{0.46}`: with `μ + ν + π + η = 1` for `h = x^η`. -/
theorem lemma15 {μ ν π η : ℝ} (hμν : μ ≤ ν) (hν : ν ≤ 0.4) (hπ0 : 0 ≤ π) (hπ : π < 0.1)
    (hpm : 0.46 < μ + π) (hsum : μ + ν + π + η = 1) :
    η ≤ 1.1 - 2 * π - μ - ν ∧ 1.1 - 2 * π - μ - ν ≤ 1.1 - 2 * (π + μ) ∧
      1.1 - 2 * (π + μ) ≤ 0.18 ∧ μ + π - ν ≤ π ∧ ν - (μ + π) < 0 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 16, `t_k`: `mp < x^{(α+2)/10}` when `M ≤ x^{(α+1)/10}` and
`p < (x^{1.1}/M²)^{1/(9-2α)}`, for `0 ≤ α ≤ 3`. -/
theorem lemma16_mp {α μ π : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 3) (hμ : μ ≤ (α + 1) / 10)
    (hπ : π * (9 - 2 * α) < 1.1 - 2 * μ) : μ + π < (α + 2) / 10 := by
  have h9 : 0 < 9 - 2 * α := by linarith
  have key : (μ + π) * (9 - 2 * α) < (α + 2) / 10 * (9 - 2 * α) := by
    nlinarith [mul_le_mul_of_nonneg_right hμ (by linarith : (0 : ℝ) ≤ 7 - 2 * α)]
  exact lt_of_mul_lt_mul_right key h9.le

theorem lemma16_half {α : ℝ} (hα : α ≤ 3) : (α + 2) / 10 ≤ 1 / 2 := by linarith

/-- `mp ≥ M x^{0.1} ≥ x^{(α+1)/10}`, so the new level `β` is at least `α + 1`. -/
theorem lemma16_beta {α μ π : ℝ} (hμ : α / 10 ≤ μ) (hπ : 0.1 ≤ π) : (α + 1) / 10 ≤ μ + π := by
  linarith

/-- The first hypothesis of (4.23) at level `β`: from `p^{9-2α} M² ≤ x^{1.1}` and `β ≥ α + 1`,
`p^{11-2β} M² ≤ x^{1.1}`, that is `p ≪ (x^{1.1}/(M²p²))^{1/(9-2β)}`. -/
theorem lemma16_first {α β μ π : ℝ} (hβ : α + 1 ≤ β) (hπ : 0 ≤ π)
    (h423 : π * (9 - 2 * α) + 2 * μ ≤ 1.1) : π * (11 - 2 * β) + 2 * μ ≤ 1.1 := by
  nlinarith [mul_le_mul_of_nonneg_left hβ hπ]

/-- The second: `MN ≤ x^{0.775} z^{α-4}` with `p < z`, `α ≤ 4`, `β ≥ α + 1` gives
`MpN ≤ x^{0.775} p^{β-4}`. -/
theorem lemma16_second {α β μ ν π ζ : ℝ} (hα : α ≤ 4) (hβ : α + 1 ≤ β) (hπ : 0 ≤ π)
    (hπζ : π ≤ ζ) (h423 : μ + ν ≤ 0.775 + (α - 4) * ζ) :
    μ + π + ν ≤ 0.775 + (β - 4) * π := by
  have h1 : (α - 4) * ζ ≤ (α - 4) * π := mul_le_mul_of_nonpos_left hπζ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hβ hπ]

end LeanLab.BHP1997.Lemma1516
