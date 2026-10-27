/-
P0069 Baker, Harman, Pintz 1997, Lemma 10, pages 23 and 24, read from the page images
papers/P0069-original.pdf. Unit U-5067, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`, powers of ℒ dropped since every saving below is a power of `x`
or a power of `T₀ = exp(ℒ^{1/3})`: `t` for `T`, `0 ≤ t ≤ t₁ = 0.45 - 2ε/3`; `m, n, l` for
`M, N, L`, `m + n + l = 1`; (3.38) `max(m, 0.45) + max(n, 0.225) ≤ 0.775 + ε/8`.
PROVED: the case `L > qT`, `(T₁ + M)^{1/2}(T₁ + N)^{1/2}` gives `T₁`, `T₁^{1/2} x^{0.275+ε/16}` and
`x^{1/2} T₀^{-1/2}`, all `≪ x^{1/2}ℒ^{-A}`; under (3.38) `(T + M)^{1/2}(T + N²)^{1/4}` is at
most `x^{0.3875 + ε/16}` and the `T^{1/4}` term saves `x^{5ε/48}`; and every term of the
remaining product with the factor `L^{1/2} T^{-1/4}` as printed is `≪ x^{1/2}ℒ^{-A}`, because the
case `L ≤ qT` with (3.38) forces `N ≥ x^{13ε/24}` and `M ≥ x^{0.225 + 13ε/24}`, or carries
`T^{-1/4} ≤ T₀^{-1/4}`. Lemma 9 would give the sharper `L^{1/2} T^{-3/4}`; the printed factor
suffices. MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma10

/-- (3.38) bounds `M ≤ x^{0.55 + ε/8}` and `N ≤ x^{0.325 + ε/8}`, and (3.39) bounds both by
`x^{0.46 + ε/8}`; either way `max(M, N) ≤ x^{0.55 + ε/8}`. -/
theorem lengths_of_338 {ε m n : ℝ} (h : max m 0.45 + max n 0.225 ≤ 0.775 + ε / 8) :
    m ≤ 0.55 + ε / 8 ∧ n ≤ 0.325 + ε / 8 := by
  have := le_max_left m 0.45; have := le_max_right m 0.45
  have := le_max_left n 0.225; have := le_max_right n 0.225
  constructor <;> linarith

/-- The case `L > qT`: `T₁ < x^{1/2}` and `T₁^{1/2} x^{0.275 + ε/16} = x^{1/2 - 13ε/48}`. -/
theorem case_L_gt {ε : ℝ} (hε : 0 < ε) :
    0.45 - 2 * ε / 3 < 1 / 2 ∧ (0.45 - 2 * ε / 3) / 2 + (0.275 + ε / 16) = 1 / 2 - 13 * ε / 48 := by
  constructor
  · linarith
  · ring

/-- Under (3.38), for `0 ≤ t ≤ 0.45`: `max(t, m)/2 + max(t, 2n)/4 ≤ 0.3875 + ε/16`. -/
theorem prod_338 {ε m n t : ℝ} (ht : t ≤ 0.45)
    (h : max m 0.45 + max n 0.225 ≤ 0.775 + ε / 8) :
    max t m / 2 + max t (2 * n) / 4 ≤ 0.3875 + ε / 16 := by
  have h1 : max t m ≤ max m 0.45 := max_le (le_trans ht (le_max_right _ _)) (le_max_left _ _)
  have h2 : max t (2 * n) ≤ 2 * max n 0.225 :=
    max_le (by linarith [le_max_right n 0.225]) (by linarith [le_max_left n 0.225])
  linarith

/-- The `T^{1/4}` term: `x^{0.3875 + ε/16} T₁^{1/4} = x^{1/2 - 5ε/48}`. -/
theorem T_quarter_term (ε : ℝ) :
    0.3875 + ε / 16 + (0.45 - 2 * ε / 3) / 4 = 1 / 2 - 5 * ε / 48 := by ring

/-- In the case `L ≤ qT`, (3.38) forces `N ≥ x^{13ε/24}` and `M ≥ x^{0.225 + 13ε/24}`. -/
theorem lower_lengths {ε m n l : ℝ} (hsum : m + n + l = 1) (hl : l ≤ 0.45 - 2 * ε / 3)
    (h : max m 0.45 + max n 0.225 ≤ 0.775 + ε / 8) :
    13 * ε / 24 ≤ n ∧ 0.225 + 13 * ε / 24 ≤ m := by
  obtain ⟨hm, hn⟩ := lengths_of_338 h
  constructor <;> linarith

/-- The remaining product with the printed factor `L^{1/2} T^{-1/4}`: its four terms are
`T^{1/2}·T^{1/4}`, `T^{1/2}·N^{1/2}`, `M^{1/2}·T^{1/4}`, `M^{1/2}·N^{1/2}`, times
`L^{1/2} T^{-1/4}`. The first three save a power of `x`; the last is `x^{1/2} T^{-1/4}`, saved
by `T ≥ T₀`. -/
theorem remaining_terms {ε m n l t : ℝ} (hε : 0 < ε) (hsum : m + n + l = 1) (ht0 : 0 ≤ t)
    (ht : t ≤ 0.45 - 2 * ε / 3) (hl : l ≤ 0.45 - 2 * ε / 3)
    (h : max m 0.45 + max n 0.225 ≤ 0.775 + ε / 8) :
    t / 2 + t / 4 + l / 2 - t / 4 ≤ 1 / 2 - ε / 30 ∧
      t / 2 + n / 2 + l / 2 - t / 4 ≤ 1 / 2 - 13 * ε / 48 ∧
      m / 2 + t / 4 + l / 2 - t / 4 ≤ 1 / 2 - 13 * ε / 48 ∧
      m / 2 + n / 2 + l / 2 - t / 4 = 1 / 2 - t / 4 := by
  obtain ⟨hn, hm⟩ := lower_lengths hsum hl h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end LeanLab.BHP1997.Lemma10
