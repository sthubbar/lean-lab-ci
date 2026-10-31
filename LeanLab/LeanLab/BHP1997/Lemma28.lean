/-
P0069 Baker, Harman, Pintz 1997, Lemma 28, pages 41 and 42, read from the page images
papers/P0069-original.pdf. Unit U-5089, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`, `0.1 ≤ n₁ ≤ ⋯ ≤ n₆`, `n₁ + ⋯ + n₆ = 1`, with Lemma 17 (a)
excluding a subproduct in `[0.4, 0.46]`.
PROVED, the exponent steps listed here: `n₁n₂n₃ < x^{0.4}` gives `n₅n₆ ≥ x^{0.4}`; with `n₁n₂n₃n₄ ≥ x^{0.46}`,
`n₂n₃n₄ ≤ x^{0.44}`; `n₆ < x^{0.3}` puts `n₁n₆, n₂n₃n₄, n₅` in Lemma 4's range, `n₅ < x^{0.225}`;
`n₆ ≥ x^{0.3}` gives `n₁n₆ ≥ x^{0.4}` and then `n₃n₄n₅ ≤ x^{0.44}`; after `n₆ = p₆n₇`,
`n₁⋯n₅ ≥ x^{0.575}`, the page prints the weaker `0.57`, `p₆ ≤ x^{0.2}`, and in the case `n₁n₂ > x^{0.26}`, `n₁⋯n₅ > x^{0.65}`,
`p₆ < x^{0.175}`, `n₁n₂p₆ ≤ x^{0.4·2/3 + 0.175}`; `n₄ ≥ x^{0.15}` once `n₁n₂n₃ ≥ x^{0.46}`.
All MATCH. Also `final_grouping`, U-5098: both `n₁n₂` branches give
`max(n₃n₄n₅, n₁n₂p₆) < x^{0.4}`, the page's `x^{0.26}` branch via `0.26 + 0.2 ≤ 0.46` and
Lemma 17 (a), and `n₃n₄n₅, n₁n₂p₆, n₇` in Lemma 4's range. The five-dimensional integral of page 42 is checked numerically, gen/u1_integral.py.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma28

theorem first {a b c d e f : ℝ} (ha : 0.1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hs : a + b + c + d + e + f = 1) (h3 : a + b + c < 0.4) :
    0.4 ≤ e + f ∧ (0.46 ≤ e + f → b + c + d ≤ 0.44) := by
  refine ⟨by linarith, fun h => by linarith⟩

theorem small_n6 {a b c d e f : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hef : e ≤ f) (hs : a + b + c + d + e + f = 1) (h3 : a + b + c < 0.4)
    (h6 : f < 0.3) (hbcd : b + c + d ≤ 0.44) (h5 : e < 0.225) :
    a + f < 0.46 ∧ b + c + d ≤ 0.46 ∧ e < 8 / 35 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem big_n6 {a b c d e f : ℝ} (ha : 0.1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e + f = 1) (h6 : 0.3 ≤ f) :
    0.4 ≤ a + f ∧ (0.46 ≤ a + f → c + d + e ≤ 0.44) := by
  refine ⟨by linarith, fun h => by linarith⟩

/-- After `n₆ = p₆n₇`, `n₇ ≥ p₆`, with `n₁n₂n₃n₄ ≥ x^{0.46}` and `n₆ < x^{0.4}` by Lemma 17 (a). -/
theorem split_n6 {a b c d e f p : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e + f = 1) (h4 : 0.46 ≤ a + b + c + d)
    (hf : f < 0.4) (hp : 2 * p ≤ f) :
    0.575 ≤ a + b + c + d + e ∧ 0.6 < a + b + c + d + e ∧ p ≤ 0.2 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem big_n1n2 {a b c d e f p : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e + f = 1) (h12 : 0.26 < a + b) (h3 : a + b + c < 0.4)
    (hp : 2 * p ≤ f) :
    0.65 < a + b + c + d + e ∧ p < 0.175 ∧ a + b + p ≤ 0.4 * (2 / 3) + 0.175 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The final step, both branches `n₁n₂ ≤ x^{0.26}` and `n₁n₂ > x^{0.26}`: with `n₆ = p₆n₇`,
`p₆ ≤ n₇ < x^{0.225}` and Lemma 17 (a) excluding `n₃n₄n₅` and `n₁n₂p₆` from `[x^{0.4}, x^{0.46}]`,
`max(n₃n₄n₅, n₁n₂p₆) < x^{0.4}`, `n₇ < x^{8/35}`, which is Lemma 4's range (3.30). -/
theorem final_grouping {a b c d e f p n : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e + f = 1) (h3 : a + b + c < 0.4)
    (h4 : 0.46 ≤ a + b + c + d) (hf : f < 0.4) (hfp : f = p + n) (hpn : p ≤ n)
    (hn : n < 0.225) (hcde : c + d + e ≤ 0.44)
    (x1 : c + d + e < 0.4 ∨ 0.46 < c + d + e) (x2 : a + b + p < 0.4 ∨ 0.46 < a + b + p) :
    c + d + e < 0.4 ∧ a + b + p < 0.4 ∧ n < 8 / 35 ∧ (c + d + e) + (a + b + p) + n = 1 := by
  have hp : p ≤ 0.2 := (split_n6 hab hbc hcd hde hs h4 hf (by linarith)).2.2
  have hab2 : a + b + p ≤ 0.46 := by
    rcases le_or_gt (a + b) 0.26 with h | h
    · linarith
    · have := (big_n1n2 hab hbc hcd hde hs h h3 (show 2 * p ≤ f by linarith)).2.2
      linarith
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · rcases x1 with h | h
    · exact h
    · linarith
  · rcases x2 with h | h
    · exact h
    · linarith

theorem n4_ge {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (h : 0.46 ≤ a + b + c) :
    0.15 ≤ d := by linarith

end LeanLab.BHP1997.Lemma28
