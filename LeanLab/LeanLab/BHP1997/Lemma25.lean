/-
P0069 Baker, Harman, Pintz 1997, Lemma 25 and the rest of page 39, read from the page images
papers/P0069-original.pdf. Unit U-5087, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`; `n₃ = 1 - a₁ - a₂`, `n₃ = p₃n₄` with `n₄ ≥ p₃`, then
`p₁ = p₄n₅` with `n₅ ≥ p₄`.
PROVED, every exponent step under (4.32): `n₄ ≤ x^{0.5}`, `n₄p₂p₃ ≤ x^{0.7}`; `p₂p₄ > x^{0.46}` gives
`p₂p₁^{1/2} > x^{0.46}`; if `p₂p₃ < x^{0.4}` then `p₄n₄ < x^{0.44}`; `p₃ > x^{0.16}`,
`n₄ ≥ x^{0.18}`, `n₅ ≥ x^{0.15}`. Under (4.33), `n₃ ∈ [x^{0.3}, x^{0.4}]` and `n₃p₂ ∈ [x^{0.6}, x^{0.64}]`.
The last paragraph: `n₃p₁ ≤ x^{0.775}` and `x^{1.1}/p₁² > p₂^{1/2}` from `a₂ ≥ 0.225` and
`4a₁ + a₂ < 2.2`; Lemma 14's `M ≤ x^{0.5}` holds as `p₁ < x^{1/2}` in `c_k(3)`. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma25

theorem case432 {a1 a2 a3 n4 a4 e : ℝ} (h1 : 0.3 ≤ a1) (h2 : 0.225 ≤ a2) (h2' : a2 ≤ 0.3)
    (h12 : 0.6 ≤ a1 + a2) (h12' : a1 + a2 ≤ 0.64) (hn3 : a3 + n4 = 1 - a1 - a2)
    (h3 : 0.1 ≤ a3) (h3n : a3 ≤ n4) (hp1 : a1 = a4 + e) (h4e : a4 ≤ e) :
    n4 ≤ 0.5 ∧ n4 + a2 + a3 ≤ 0.7 ∧ (0.46 < a2 + a4 → 0.46 < a2 + a1 / 2) ∧
      (0.46 < a2 + a1 / 2 → a4 + n4 ≤ a1 / 2 + (0.9 - a1 - a2) ∧ a1 / 2 + (0.9 - a1 - a2) < 0.44) ∧
      (0.46 < a2 + a3 → 0.16 < a3) ∧ 0.18 ≤ n4 ∧ 0.15 ≤ e := by
  refine ⟨by linarith, by linarith, fun h => by linarith, fun h => ⟨by linarith, by linarith⟩,
    fun h => by linarith, by linarith, by linarith⟩

theorem case433 {a1 a2 : ℝ} (h1 : 0.36 ≤ a1) (h1' : a1 ≤ 0.4) (h2' : a2 ≤ 0.3)
    (h12 : 0.6 ≤ a1 + a2) :
    0.3 ≤ 1 - a1 - a2 ∧ 1 - a1 - a2 ≤ 0.4 ∧ 0.6 ≤ (1 - a1 - a2) + a2 ∧
      (1 - a1 - a2) + a2 ≤ 0.64 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem last_para {a1 a2 : ℝ} (h2 : 0.225 ≤ a2) (h4 : 4 * a1 + a2 < 2.2) :
    (1 - a1 - a2) + a1 ≤ 0.775 ∧ a2 / 2 < 1.1 - 2 * a1 := by
  constructor <;> linarith

end LeanLab.BHP1997.Lemma25
