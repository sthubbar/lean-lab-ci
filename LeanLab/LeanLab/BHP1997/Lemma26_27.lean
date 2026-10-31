/-
P0069 Baker, Harman, Pintz 1997, Lemmas 26 and 27, page 40, read from the page images
papers/P0069-original.pdf. Unit U-5088, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`.
PROVED, the exponent steps listed here: Lemma 26, `MN² ≤ x^{0.82}` gives `n₄ ≥ x^{0.18}`, and with
`n₄ < x^{0.225}`, `p₃n₄² ≥ x^{2-0.5-0.82-0.225} = x^{0.455} > x^{0.45}`. FINDING, cosmetic: the page
writes `n₄p₃² = (p₁p₂p₃n₄)²/(p₁²p₂²p₃)`, whose right side is `p₃n₄²`; the printed `n₄p₃² > x^{0.45}`
also holds there, by `lemma26_printed_true`, so Lemma 3 (iii) applies either way. Lemma 27, `a₂ ≥ 0.18` with
(4.34) excluded forces `a₁ + a₂ > 0.7`, so `p₂ > x^{0.2}`, `n₃ < x^{0.3}`; `p₂ ≤ x^{0.27}`;
`p₃n₅ ≤ x^{0.45}`; `n₅²p₂ ≥ x^{0.5}`. The branch `a₂ ≤ 0.15`: `p₄n₅ ≤ x^{0.34} < x^{0.4}`, and
Lemma 3 (iv), `p₂p₃ ≥ x^{0.275} ≥ x^{9/35}`, `p₂p₃n₄ ≥ x^{0.5} > x^{63/130}`; with the hypothesis `a₂ ≤ 0.15` and both cases,
`lemma27_le015`. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma2627

/-- Lemma 26: `n₄ ≥ x^{0.18}`; the displayed quantity `(p₁p₂p₃n₄)²/(p₁²p₂²p₃)` is `p₃n₄²`, at
least `x^{2-0.5-0.82-0.225} = x^{0.455}`. -/
theorem lemma26 {a1 a2 a3 n4 : ℝ} (h1 : a1 ≤ 0.5) (h12 : a1 + 2 * a2 ≤ 0.82) (h32 : a3 ≤ a2)
    (h3n : a3 ≤ n4) (hn : n4 < 0.225) (hs : a1 + a2 + a3 + n4 = 1) :
    0.18 ≤ n4 ∧ 2 * (a1 + a2 + a3 + n4) - (2 * a1 + 2 * a2 + a3) = a3 + 2 * n4 ∧
      2 - a1 - (a1 + 2 * a2) - a3 = a3 + 2 * n4 ∧
      (0.45 : ℝ) < 2 - 0.5 - 0.82 - 0.225 ∧ 2 - 0.5 - 0.82 - 0.225 ≤ a3 + 2 * n4 := by
  refine ⟨by linarith, by ring, by linarith, by norm_num, by linarith⟩

/-- FINDING, cosmetic: the page writes the left side as `n₄p₃²`, but the identity gives `p₃n₄²`;
at `(a₁, a₂, a₃, n₄) = (0.5, 0.16, 0.12, 0.22)` the two differ, `0.46` against `0.56`. -/
theorem lemma26_identity_misprint :
    (0.5 : ℝ) + 0.16 + 0.12 + 0.22 = 1 ∧ (0.12 : ℝ) + 2 * 0.22 ≠ 0.22 + 2 * 0.12 := by
  constructor <;> norm_num

/-- The printed `n₄p₃² ≥ x^{0.45}` is still true in the case `n₄ < x^{0.225}`, since that case
forces `a₃ > 0.115`: `n₄ + 2a₃ > 0.455`. -/
theorem lemma26_printed_true {a1 a2 a3 n4 : ℝ} (h1 : a1 ≤ 0.5) (h12 : a1 + 2 * a2 ≤ 0.82)
    (hn : n4 < 0.225) (hs : a1 + a2 + a3 + n4 = 1) : 0.115 < a3 ∧ 0.455 < n4 + 2 * a3 := by
  constructor <;> linarith

/-- Lemma 27, `a₂ ≥ 0.18`: with `0.46 ≤ a₁ ≤ 0.5`, `a₁ + a₂ ≥ 0.64` always, so excluding (4.34)
leaves `a₁ + a₂ > 0.7`. -/
theorem lemma27_region {a1 a2 : ℝ} (h1 : 0.46 ≤ a1) (h1' : a1 ≤ 0.5) (h2 : 0.18 ≤ a2)
    (h12 : a1 + 2 * a2 ≤ 1) (hx : ¬ (0.64 ≤ a1 + a2 ∧ a1 + a2 ≤ 0.7)) :
    0.7 < a1 + a2 ∧ 0.2 < a2 ∧ 1 - a1 - a2 < 0.3 ∧ a2 ≤ 0.27 := by
  have h7 : 0.7 < a1 + a2 := by
    by_contra h; push Not at h; exact hx ⟨by linarith, h⟩
  refine ⟨h7, by linarith, by linarith, by linarith⟩

/-- `p₁ = p₃n₄`, `n₃ = p₄n₅`, `p₃ ≤ n₄`, `p₄ ≥ 0.1`: `p₃n₅ ≤ x^{0.45}` and `n₅²p₂ ≥ x^{0.5}`. -/
theorem lemma27_steps {a1 a2 a3 n4 a4 e : ℝ} (h1' : a1 ≤ 0.5) (hp1 : a1 = a3 + n4) (h3n : a3 ≤ n4)
    (hn3 : 1 - a1 - a2 = a4 + e) (hn3' : 1 - a1 - a2 < 0.3) (h4 : 0.1 ≤ a4) (h4e : a4 ≤ e) :
    a3 + e ≤ 0.5 / 2 + (0.3 - 0.1) ∧ 0.5 / 2 + (0.3 - 0.1) = (0.45 : ℝ) ∧ 0.5 ≤ 2 * e + a2 := by
  refine ⟨by linarith, by norm_num, by linarith⟩

/-- `p₄n₅ = n₄ ≤ x^{1-0.46-0.1-0.1}`, which the page uses in its `p₂p₃ ≤ x^{0.275}` branch and
which holds without `h23`; under `h23`, the `p₂p₃ ≥ x^{0.275}` branch, Lemma 3 (iv). The page's
hypothesis `a₂ ≤ 0.15` and its conclusion `p₃ ≤ x^{0.15}` are NOT formalized here. -/
theorem lemma27_small {a1 a2 a3 n : ℝ} (h1 : 0.46 ≤ a1) (h1' : a1 ≤ 0.5) (h2 : 0.1 ≤ a2)
    (h3 : 0.1 ≤ a3) (h23 : 0.275 ≤ a2 + a3) (hs : a1 + a2 + a3 + n = 1) :
    n ≤ 1 - 0.46 - 0.1 - 0.1 ∧ (1 - 0.46 - 0.1 - 0.1 : ℝ) < 0.4 ∧ (9 / 35 : ℝ) ≤ a2 + a3 ∧
      0.5 ≤ a2 + a3 + n ∧ (63 / 130 : ℝ) < 0.5 := by
  refine ⟨by linarith, by norm_num, by linarith, by linarith, by norm_num⟩

/-- Branch `a₂ ≤ 0.15` with its hypothesis, U-5099. Case `p₂p₃ ≤ x^{0.275}`: `p₄n₅ = n₄ ≤ x^{0.34} < x^{0.4}`.
Case `p₂p₃ ≥ x^{0.275}`: the four inputs of Lemma 3 (iv), `p₂p₃ ≥ x^{9/35}`, `p₃ ≤ p₂ ≤ x^{0.15}`,
`p₂p₃n₄ ≥ x^{0.5}`, `p₁ ≥ x^{0.46}`. -/
theorem lemma27_le015 {a1 a2 a3 n : ℝ} (h1 : 0.46 ≤ a1) (h1' : a1 ≤ 0.5) (h2 : 0.1 ≤ a2)
    (h2' : a2 ≤ 0.15) (h3 : 0.1 ≤ a3) (h32 : a3 ≤ a2) (hs : a1 + a2 + a3 + n = 1) :
    (a2 + a3 ≤ 0.275 → n ≤ 1 - 0.46 - 0.1 - 0.1 ∧ n < 0.4) ∧
      (0.275 ≤ a2 + a3 → 9 / 35 ≤ a2 + a3 ∧ a3 ≤ a2 ∧ a2 ≤ 0.15 ∧ 0.5 ≤ a2 + a3 + n ∧ 0.46 ≤ a1) := by
  refine ⟨fun _ => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, h32, h2', by linarith, h1⟩⟩

end LeanLab.BHP1997.Lemma2627
