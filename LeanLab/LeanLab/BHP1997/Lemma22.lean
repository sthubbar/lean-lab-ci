/-
P0069 Baker, Harman, Pintz 1997, Lemma 22, page 36, read from the page images
papers/P0069-original.pdf. Unit U-5084, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`, `a₁ ≥ a₂ ≥ a₃ ≥ a₄ ≥ 0.1` for `p₁, ..., p₄`, `e` for `n₅`,
`a₁ + a₂ + a₃ + a₄ + e = 1`, `M = p₁`, `N = p₂`.
PROVED, every exponent step: under (4.26), `p₁p₂ ≤ x^{0.5}`, `p₁p₂p₃ < x^{0.775}`, and with
Lemma 14's `p₄ ≥ x^{1.1}/(p₁p₂)²`, `p₁p₄ ≥ x^{0.4}`; once `p₁p₄ ≥ x^{0.46}`, `p₄, p₃, n₅ ≥ x^{0.16}`.
Under (4.27), `n₅ ≥ x^{0.18}`, `n₅p₄² ≥ x^{1.1 - 0.1 - 1.64/3} > x^{0.45}` with margin
`0.0033`, and the case `p₃ < x^{0.15}` is empty, `n₅p₃ > x^{0.4}` against `n₅p₃ ≤ x^{0.44}`
with `n₅p₃ ∉ [x^{0.4}, x^{0.46}]`. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma22

theorem case426 {a1 a2 a3 a4 : ℝ} (h1 : a1 ≤ 0.3) (h12 : a1 + 2 * a2 ≤ 0.7) (h23 : a3 ≤ a2)
    (h4 : 1.1 - 2 * (a1 + a2) ≤ a4) :
    a1 + a2 ≤ 0.5 ∧ a1 + a2 + a3 < 0.775 ∧ 0.4 ≤ a1 + a4 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem case426b {a1 a3 a4 e : ℝ} (h1 : a1 ≤ 0.3) (h14 : 0.46 ≤ a1 + a4) (h34 : a4 ≤ a3)
    (h4e : a4 ≤ e) : 0.16 ≤ a4 ∧ 0.16 ≤ a3 ∧ 0.16 ≤ e := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem case427 {a1 a2 a3 a4 e : ℝ} (h1 : a1 ≤ 0.3) (h13 : a1 + 3 * a2 ≤ 0.82)
    (h23 : a3 ≤ a2) (h34 : a4 ≤ a3) (h4 : 0.1 ≤ a4) (hs : a1 + a2 + a3 + a4 + e = 1) :
    0.18 ≤ e ∧ 1.1 - 0.1 - 1.64 / 3 ≤ 1.1 - a1 / 3 - 2 / 3 * (a1 + 3 * a2) ∧
      (0.45 : ℝ) + 0.0033 < 1.1 - 0.1 - 1.64 / 3 := by
  refine ⟨by linarith, by linarith, by norm_num⟩

/-- `n₅p₄² ≥ x p₄/(p₁p₂²) ≥ x^{1.1}/(p₁p₂²)`, the chain of the page, with `p₄ ≥ x^{0.1}`. -/
theorem case427_chain {a1 a2 a3 a4 e : ℝ} (h23 : a3 ≤ a2) (h4 : 0.1 ≤ a4)
    (hs : a1 + a2 + a3 + a4 + e = 1) :
    1 + a4 - (a1 + 2 * a2) ≤ e + 2 * a4 ∧ 1.1 - (a1 + 2 * a2) ≤ 1 + a4 - (a1 + 2 * a2) ∧
      a1 + 2 * a2 = a1 / 3 + 2 / 3 * (a1 + 3 * a2) := by
  refine ⟨by linarith, by linarith, by ring⟩

/-- The subcase `p₃ < x^{0.15}` is empty: `p₁p₃ < x^{0.45}`, and so `p₁p₃ < x^{0.4}` by
Lemma 17 (a), the hypothesis `h13'`; `p₂ < x^{0.2}`; then `n₅p₃ > x^{0.4}`, while
`n₅p₃ ≤ x^{0.54}/p₄ ≤ x^{0.44}` once `p₁p₂ ≥ x^{0.46}`. -/
theorem case427_empty {a1 a2 a3 a4 e : ℝ} (h0 : 0.23 ≤ a1) (h1 : a1 ≤ 0.3) (h13 : a1 + 3 * a2 ≤ 0.82)
    (h12 : 0.46 ≤ a1 + a2) (h3 : a3 < 0.15) (h4 : 0.1 ≤ a4) (h34 : a4 ≤ a3)
    (h13' : a1 + a3 < 0.4) (hs : a1 + a2 + a3 + a4 + e = 1) :
    a1 + a3 < 0.45 ∧ a2 < 0.2 ∧ 0.4 < e + a3 ∧ e + a3 ≤ 0.44 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end LeanLab.BHP1997.Lemma22
