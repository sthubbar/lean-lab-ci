/-
P0069 Baker, Harman, Pintz 1997, page 38: the region (4.29) and Lemma 24, read from the page
images papers/P0069-original.pdf. Unit U-5086, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`.
PROVED: in (4.29), `0.3 ≤ a₁ ≤ 0.4`, `a₁ + a₂ ≥ 0.6`, `a₁ + 2a₂ ≤ 1`, the case `a₂ ≤ 0.225` meets
Lemma 4's (3.30), `max(p₁, n₃) ≤ x^{0.4}` and `L = p₂ ≤ x^{0.225} < x^{8/35}`; Lemma 24 under (4.30),
`p₃n₄ ∈ [x^{0.36}, x^{0.4}]`, `n₄ ≥ x^{0.18}`, `p₁p₄ ≥ x^{0.4}`, `n₅ ≥ x^{0.15}`,
`n₄p₃² ≥ x^{0.46}`. All MATCH. The page writes `n₆ ≥ 0.18` for `n₆ ≥ x^{0.18}`, typographical.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma24

/-- (4.29) with `a₂ ≤ 0.225` is Lemma 4's range: `M = p₁`, `N = n₃ = x/(p₁p₂)`, `L = p₂`. -/
theorem region429 {a1 a2 : ℝ} (h1 : 0.3 ≤ a1) (h1' : a1 ≤ 0.4) (h12 : 0.6 ≤ a1 + a2)
    (h2 : a2 ≤ 0.225) : a1 ≤ 0.46 ∧ 1 - a1 - a2 ≤ 0.4 ∧ a2 < 8 / 35 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Lemma 24 under (4.30): `M = p₁ ≥ 0.3`, `N = p₂ ≥ 0.3`, `MN ≤ 0.64`, `p₃n₄ = x/(MN)`,
`n₄ ≥ p₃`, then `p₂ = p₄n₅` with `n₅ ≥ p₄ ≥ 0.1`. -/
theorem case430 {a1 a2 a3 n4 a4 e : ℝ} (h1 : 0.3 ≤ a1) (h2 : 0.3 ≤ a2) (h12 : a1 + a2 ≤ 0.64)
    (hs : a1 + a2 + a3 + n4 = 1) (h34 : a3 ≤ n4) (h3 : 0.1 ≤ a3) (h4 : 0.1 ≤ a4)
    (h2s : a2 = a4 + e) (h4e : a4 ≤ e) :
    0.36 ≤ a3 + n4 ∧ a3 + n4 ≤ 0.4 ∧ 0.18 ≤ n4 ∧ 0.4 ≤ a1 + a4 ∧ 0.15 ≤ e ∧
      0.46 ≤ n4 + 2 * a3 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end LeanLab.BHP1997.Lemma24
