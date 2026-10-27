/-
P0069 Baker, Harman, Pintz 1997, Lemma 23 and the paragraph after it, page 37, read from the page
images papers/P0069-original.pdf. Unit U-5085, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`; `a₁ ≥ a₂ ≥ a₃ ≥ a₄ ≥ 0.1`, `e ≥ a₄` for `n₅`, sums equal to 1.
Region: `0.23 ≤ a₁ ≤ 0.3`, `0.7 ≤ a₁ + 2a₂`, `0.46 ≤ a₁ + a₂ ≤ 0.54`.
PROVED, every exponent step: `p₁p₂p₃ ≤ x^{0.77}` and `p₂p₃ ≤ x^{0.5}`, the latter tight and using
`p₂ ≤ p₁`; `p₃n₅ ≤ x^{0.44}`; when `p₁p₄ > x^{0.46}`, `p₂ ≥ x^{0.2}`, `p₃ ≥ x^{0.16}`,
`p₂p₄n₅ ≥ x^{0.43}`, `p₂n₅² ≥ p₂p₄n₅`; Lemma 13 covers `a₁ + a₂ ≥ 0.54`, as `a₁ + a₂ ≤ 0.6`;
the covered sub-region `p₂ ≥ x^{0.225}`, `p₁⁴p₂³ ≥ x^{1.8}`, `p₁p₂ ≤ x^{0.54}` fits Lemma 14 with
`M = n₃`, `N = p₁`, and `z > p₂^{1/2}` there is exactly `4a₁ + 3a₂ > 1.8`. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma23

/-- After decomposing to `p₁p₂p₃n₄`, `n₄ ≥ p₃`: `p₁p₂p₃ ≤ x^{0.77}` and, with `p₂ ≤ p₁`,
`p₂p₃ ≤ x^{0.5}`. Equality at `a₁ = a₂ = 0.27`, `a₃ = 0.23`. -/
theorem first_step {a1 a2 a3 n : ℝ} (h12 : a1 + a2 ≤ 0.54) (h21 : a2 ≤ a1) (h3n : a3 ≤ n)
    (hs : a1 + a2 + a3 + n = 1) : a1 + a2 + a3 ≤ 0.77 ∧ a2 + a3 ≤ 0.5 := by
  constructor <;> linarith

theorem first_step_tight :
    (0.27 : ℝ) + 0.27 ≤ 0.54 ∧ (0.27 : ℝ) + 2 * 0.27 ≥ 0.7 ∧ (0.27 : ℝ) + 0.23 = 0.5 ∧
      (0.27 : ℝ) + 0.27 + 2 * 0.23 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `p₃n₅ = x/(p₁p₂p₄) ≤ x^{0.44}`. -/
theorem p3n5 {a1 a2 a3 a4 e : ℝ} (h12 : 0.46 ≤ a1 + a2) (h4 : 0.1 ≤ a4)
    (hs : a1 + a2 + a3 + a4 + e = 1) : a3 + e ≤ 0.44 := by linarith

/-- `p₁p₄ > x^{0.46}`: `p₂ ≥ x^{0.2}`, `p₃ ≥ x^{0.16}`, `p₂p₄n₅ ≥ x^{0.43}`, `p₂n₅² ≥ p₂p₄n₅`. -/
theorem big_p1p4 {a1 a2 a3 a4 e : ℝ} (h1 : a1 ≤ 0.3) (h2 : 0.7 ≤ a1 + 2 * a2)
    (h12 : 0.46 ≤ a1 + a2) (h34 : a4 ≤ a3) (h4e : a4 ≤ e) (h3 : 2 * a3 ≤ 1 - a1 - a2)
    (h14 : 0.46 < a1 + a4) (hs : a1 + a2 + a3 + a4 + e = 1) :
    0.2 ≤ a2 ∧ 0.16 ≤ a3 ∧ 0.43 ≤ a2 + a4 + e ∧ a2 + a4 + e ≤ a2 + 2 * e := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 13 covers `a₁ + a₂ ≥ 0.54`: with `a₂ ≤ a₁ ≤ 0.3`, `x/(p₁p₂) ∈ [x^{0.4}, x^{0.46}]`. -/
theorem lemma13_covers {a1 a2 : ℝ} (h1 : a1 ≤ 0.3) (h21 : a2 ≤ a1) (h : 0.54 ≤ a1 + a2) :
    0.4 ≤ 1 - a1 - a2 ∧ 1 - a1 - a2 ≤ 0.46 := by
  constructor <;> linarith

/-- The covered sub-region: `n₃ ∈ (x^{0.46}, x^{0.5}]`, `p₁n₃ ≤ x^{0.775}`, and with
`z = x^{1.1}/n₃² = x^{-0.9}p₁²p₂²`, `z > p₂^{1/2}` iff `4a₁ + 3a₂ > 1.8`. -/
theorem covered {a1 a2 : ℝ} (h1 : a1 ≤ 0.3) (h2 : 0.225 ≤ a2) (h4 : 1.8 < 4 * a1 + 3 * a2)
    (h12 : a1 + a2 ≤ 0.54) :
    0.46 ≤ 1 - a1 - a2 ∧ 1 - a1 - a2 ≤ 0.5 ∧ a1 + (1 - a1 - a2) ≤ 0.775 ∧
      1.1 - 2 * (1 - a1 - a2) = -0.9 + 2 * a1 + 2 * a2 ∧ a2 / 2 < -0.9 + 2 * a1 + 2 * a2 := by
  refine ⟨by linarith, by linarith, by linarith, by ring, by linarith⟩

end LeanLab.BHP1997.Lemma23
