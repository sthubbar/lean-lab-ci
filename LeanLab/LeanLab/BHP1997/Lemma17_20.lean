/-
P0069 Baker, Harman, Pintz 1997, Lemmas 17 to 21, pages 33 to 36, read from the page images
papers/P0069-original.pdf. Unit U-5083, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`, each variable at least `0.1`, the variables summing to 1.
PROVED, the exponent steps listed here only: Lemma 17 (a), (b) for `j = 2`, `3`, `4`, (c);
Lemma 18 (i), (ii) and Lemma 21, `l18_ii`, `l21`; the Remark after Lemma 19,
`p₁ ≤ x^{0.305}`, `p₂ ≥ x^{0.235}`, `MN(x/p₁p₂)^{1/2} ≤ x^{0.77}`; Lemma 20, `N ≤ x^{0.24}`,
`N²z² ≤ x^{0.76}`, `np₃ < x^{0.4}`, and its last lines, `l20_final`. All MATCH except one. Also the proof of Lemma 19,
`l19_n5` and `l19_main`, U-5150. The bounds `N₃ > x^{0.15}`, `N₄ > x^{0.18}` are not needed for
these steps and are passed on to Lemma 3 (iii), not formalized here.
FINDING, cosmetic: the Remark prints `p₁p₂³ ≥ x^{1.05}`; the least value of `α₁ + 3α₂` on its
region is `1.01`, approached at `(0.305, 0.235)`, `remark19_min`, `remark19_printed_false`. What the
argument uses is `p₁p₂³ > x`, so that `n₃ < p₂²` is prime, and `1.01 > 1` gives it.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma1720

/-- Lemma 17 (a): `n_{j+1} > x^{0.14}` and a subproduct in `[x^{0.4}, x^{0.46}]` leave
`x/(n₁⋯n_l n_{j+1}) < x^{0.46}`. -/
theorem l17a {s t : ℝ} (hs : 0.4 ≤ s) (ht : 0.14 < t) : 1 - s - t < 0.46 := by linarith

/-- Lemma 17 (b), `j = 2`, variables `p₁, p₂, n₃` with `p₂ ≤ p₁`, `p₂ ≤ n₃`, all `≥ 0.1`, summing to
1, neither `p₁` nor `n₃` in `[0.4, 0.46]` by (a): not both exceed `0.46`, so two of the three are
`< 0.4`, `p₂` and one of `p₁, n₃`, and Lemma 15 applies. -/
theorem l17b2 {a b c : ℝ} (hb : 0.1 ≤ b) (hba : b ≤ a) (hbc : b ≤ c) (hs : a + b + c = 1)
    (ha : a < 0.4 ∨ 0.46 < a) (hc : c < 0.4 ∨ 0.46 < c) :
    ¬ (0.46 < a ∧ 0.46 < c) ∧ b < 0.4 ∧ (a < 0.4 ∨ c < 0.4) := by
  refine ⟨fun ⟨h1, h2⟩ => by linarith, by linarith, ?_⟩
  rcases ha with ha | ha
  · exact Or.inl ha
  · rcases hc with hc | hc
    · exact Or.inr hc
    · exfalso; linarith

/-- Lemma 17 (b), `j = 3`, `n₁ ≤ n₂ ≤ n₃ ≤ n₄`, all `≥ 0.1`: `n₃ ≤ 0.4`, `n₁n₂ ≤ 0.5`,
`n₁n₂n₃ ≤ 0.75`. -/
theorem l17b3 {a b c d : ℝ} (ha : 0.1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hs : a + b + c + d = 1) : c ≤ 0.4 ∧ a + b ≤ 0.5 ∧ a + b + c ≤ 0.75 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Lemma 17 (b), `j = 4`, `n₁ ≤ ⋯ ≤ n₅`: if `n₅ ≤ 0.225` then `0.4 ≤ n₄n₅ ≤ 0.45`; if
`max(n₁n₂, n₄) ≤ 0.275` then `n₂ ≤ 0.175` and `max(n₁n₄, n₂n₃) ≤ 0.45`. -/
theorem l17b4 {a b c d e : ℝ} (ha : 0.1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e = 1) :
    (e ≤ 0.225 → 0.4 ≤ d + e ∧ d + e ≤ 0.45) ∧
      (a + b ≤ 0.275 → d ≤ 0.275 → b ≤ 0.175 ∧ a + d ≤ 0.45 ∧ b + c ≤ 0.45) := by
  refine ⟨fun he => ⟨by linarith, by linarith⟩, fun h1 h2 => ⟨by linarith, by linarith, by linarith⟩⟩

/-- Lemma 17 (c), `j = 5`, `n₁ ≤ ⋯ ≤ n₅` with `n₁⋯n₅ ≤ x^{0.775}`: `n₁n₂n₃ ≤ 0.465 < 0.5` and
`n₄n₅ < 0.475 < 0.5`. -/
theorem l17c {a b c d e : ℝ} (ha : 0.1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hde : d ≤ e) (hs : a + b + c + d + e ≤ 0.775) :
    a + b + c ≤ 0.775 * 0.6 ∧ (0.775 * 0.6 : ℝ) < 0.5 ∧ d + e ≤ 0.775 - 0.3 ∧
      (0.775 - 0.3 : ℝ) < 0.5 := by
  refine ⟨by linarith, by norm_num, by linarith, by norm_num⟩

/-- Lemma 18 (i): `0.36 ≤ p₁ < 0.4`, `p₁ + p₂ ≤ 0.54`, `p₂ ≥ 0.15`, `p₅ ≥ 0.1`, `p₁ = p₅ + n₆`:
`p₃p₄n₅ ≤ 0.49`, `n₆p₅² ≥ x^{0.36+0.1} > x^{0.45}`, `p₃p₄n₅ ≥ 0.46`, and with `p₅ ≤ n₆`,
`n₆ ≥ 0.18`, the page's `n₆ > x^{0.18}` up to the strict sign. -/
theorem l18 {p1 p2 p5 n6 : ℝ} (h1 : 0.36 ≤ p1) (h12 : p1 + p2 ≤ 0.54) (h2 : 0.15 ≤ p2)
    (h5 : 0.1 ≤ p5) (h6 : p1 = p5 + n6) (h56 : p5 ≤ n6) :
    1 - p1 - p2 ≤ 0.49 ∧ 0.36 + 0.1 ≤ n6 + 2 * p5 ∧ (0.45 : ℝ) < 0.36 + 0.1 ∧
      0.46 ≤ 1 - p1 - p2 ∧ 0.18 ≤ n6 := by
  refine ⟨by linarith, by linarith, by norm_num, by linarith, by linarith⟩

/-- Lemma 18 (ii) and Lemma 21, whose proof repeats it, U-5152: `p₄ ≤ p₃ ≤ p₂ ≤ 0.15`,
`p₁ ≤ 0.4` strictly, with `p₂p₃p₄` outside `[0.4, 0.46]` by Lemma 17 (a): `p₂p₃p₄ ≤ x^{0.45}`, so
`max(p₁, p₂p₃p₄) < x^{0.4}`, and `p₁` in Lemma 21's `[0.3, 0.36]` is below `0.4`. -/
theorem l18_ii {p1 p2 p3 p4 : ℝ} (h1 : p1 < 0.4) (h2 : p2 ≤ 0.15) (h32 : p3 ≤ p2) (h43 : p4 ≤ p3)
    (x : p2 + p3 + p4 < 0.4 ∨ 0.46 < p2 + p3 + p4) :
    p2 + p3 + p4 ≤ 0.45 ∧ max p1 (p2 + p3 + p4) < 0.4 := by
  have h : p2 + p3 + p4 < 0.4 := by rcases x with h | h <;> linarith
  exact ⟨by linarith, max_lt h1 h⟩

theorem l21 {p1 : ℝ} (h1 : p1 ≤ 0.36) : p1 < 0.4 := by linarith

/-- The Remark after Lemma 19, contrary case `p₁p₂² > x^{0.775}`: `p₁ ≤ x^{0.305}`,
`p₂ ≥ x^{0.235}`, and `MN (x/p₁p₂)^{1/2} ≤ x^{0.77}`. -/
theorem remark19 {a b : ℝ} (hab : a + b ≤ 0.54) (h : 0.775 < a + 2 * b) (ha : a ≤ 0.36) :
    a ≤ 0.305 ∧ 0.2075 < b ∧ (a + b) + (1 - a - b) / 2 ≤ 0.77 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem remark19_b {a b : ℝ} (hab : a + b ≤ 0.54) (h : 0.775 < a + 2 * b) : 0.235 < b := by
  linarith

/-- The true minimum of `α₁ + 3α₂` there is `1.01`, so `p₁p₂³ > x` and `n₃ < p₂²` is prime. -/
theorem remark19_min {a b : ℝ} (hab : a + b ≤ 0.54) (h : 0.775 < a + 2 * b) :
    1.01 < a + 3 * b := by linarith

/-- FINDING: `p₁p₂³ ≥ x^{1.05}` fails at the interior point `(0.304, 0.2356)` of the contrary case:
`p₁p₂ = x^{0.5396} ≤ x^{0.54}`, `p₁p₂² = x^{0.7752} > x^{0.775}`, `x^{0.3} ≤ p₁ ≤ x^{0.36}`,
`p₂ ≥ x^{0.18}`, and `p₁p₂³ = x^{1.0108}`. -/
theorem remark19_printed_false :
    (0.304 : ℝ) + 0.2356 ≤ 0.54 ∧ (0.775 : ℝ) < 0.304 + 2 * 0.2356 ∧ (0.3 : ℝ) ≤ 0.304 ∧
      (0.304 : ℝ) ≤ 0.36 ∧ (0.18 : ℝ) ≤ 0.2356 ∧ (0.304 : ℝ) + 3 * 0.2356 < 1.05 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Lemma 20: `MN ≤ 0.54`, `M ≥ 0.3`, `MNz² ≤ 0.82` give `N ≤ 0.24`, `N²z² ≤ 1.06 - 0.3`,
`np₃ < Nz ≤ 0.38 < 0.4`, and `n₅ ≥ 1 - (MNz²) ≥ 0.18`. -/
theorem l20 {m n z : ℝ} (hm : 0.3 ≤ m) (hmn : m + n ≤ 0.54) (hz : m + n + 2 * z ≤ 0.82) :
    n ≤ 0.24 ∧ 2 * n + 2 * z ≤ 1.06 - 0.3 ∧ n + z ≤ 0.38 ∧ 0.18 ≤ 1 - (m + n + 2 * z) := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 20, the last lines, U-5151: on `mnp₃p₄n₅` with `p₄ ≤ p₃ ≤ z`, `p₄ ≥ 0.1`, `n₅ ≥ 0.18`,
`p₃²n₅ ≥ p₃p₄n₅ ≥ x^{0.46}`, `p₄m ≥ x^{0.4}` and by Lemma 17 (a) `p₄m > x^{0.46}`, for Lemma 3 (iii). -/
theorem l20_final {m n p3 p4 n5 z : ℝ} (hm : 0.3 ≤ m) (hmn : m + n ≤ 0.54)
    (hz : m + n + 2 * z ≤ 0.82) (h4 : 0.1 ≤ p4) (h43 : p4 ≤ p3) (h3z : p3 ≤ z)
    (hs : m + n + p3 + p4 + n5 = 1) (x : p4 + m < 0.4 ∨ 0.46 < p4 + m) :
    0.18 ≤ n5 ∧ 0.46 ≤ p3 + p4 + n5 ∧ p3 + p4 + n5 ≤ 2 * p3 + n5 ∧ 0.4 ≤ p4 + m ∧
      0.46 < p4 + m := by
  have h : 0.46 < p4 + m := by rcases x with h | h <;> linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, h⟩

/-- Proof of Lemma 19, U-5150, first step: `MN ≤ x^{0.54}`, `p₄ ≤ p₃ ≤ x^{0.15}` give
`n₅ ≥ x^{1-0.54-0.3} > x^{0.15}`. -/
theorem l19_n5 {m n p3 p4 n5 : ℝ} (hmn : m + n ≤ 0.54) (h3 : p3 ≤ 0.15) (h43 : p4 ≤ p3)
    (hs : m + n + p3 + p4 + n5 = 1) : 1 - 0.54 - 0.3 ≤ n5 ∧ (0.15 : ℝ) < 1 - 0.54 - 0.3 := by
  refine ⟨by linarith, by norm_num⟩

/-- Proof of Lemma 19, the dyadic step: `0.3 ≤ M ≤ 0.36`, `0.1 ≤ N₁ ≤ N₂ ≤ N₃ ≤ N₄`,
`M + N₁ + ⋯ + N₄ = 1`, with Lemma 17 (a) excluding `MN₁`, `N₃N₄`, `N₁N₂N₄` from
`[0.4, 0.46]`: `MN₁ ≥ x^{0.4}`, so `MN₁ > x^{0.46}`; `N₃N₄ ≤ x^{0.44}`, so `N₃N₄ < x^{0.4}`;
`N₁N₂N₄ < x^{0.4}` would force `N₃ > x^{0.24}`, absurd, so `N₁N₂N₄ > x^{0.46}` and
`N₂²N₄ > x^{0.46}`. With the page's `N₃ > 0.15`, `N₄ > 0.18`, not needed for these steps,
these are the inputs of Lemma 3 (iii). -/
theorem l19_main {M a b c d : ℝ} (hM : 0.3 ≤ M) (hM' : M ≤ 0.36) (ha : 0.1 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) (hs : M + a + b + c + d = 1)
    (x1 : M + a < 0.4 ∨ 0.46 < M + a) (x2 : c + d < 0.4 ∨ 0.46 < c + d)
    (x3 : a + b + d < 0.4 ∨ 0.46 < a + b + d) :
    0.4 ≤ M + a ∧ 0.46 < M + a ∧ c + d ≤ 0.44 ∧ c + d < 0.4 ∧ (a + b + d < 0.4 → 0.24 < c) ∧
      c < 0.2 ∧ 0.46 < a + b + d ∧ 0.46 < 2 * b + d := by
  have h1 : 0.46 < M + a := by rcases x1 with h | h <;> linarith
  have h2 : c + d < 0.4 := by rcases x2 with h | h <;> linarith
  have h3 : 0.46 < a + b + d := by
    rcases x3 with h | h
    · exfalso; linarith
    · exact h
  refine ⟨by linarith, h1, by linarith, h2, fun h => by linarith, by linarith, h3, by linarith⟩

end LeanLab.BHP1997.Lemma1720
