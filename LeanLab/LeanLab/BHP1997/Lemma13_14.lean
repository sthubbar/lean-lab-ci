/-
P0069 Baker, Harman, Pintz 1997, Lemmas 13 and 14, pages 28 to 30, read from the page images
papers/P0069-original.pdf. Unit U-5081, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`, `m, n` for `M, N`, `p, h, q` for the primes, `mnph = 1`.
PROVED, every exponent step of both proofs: Lemma 13, the case `N > x^{0.375}` lands in Lemma 4
with `L < x^{0.225} < x^{8/35}`; (4.20) and `Nh ≥ x^{0.46}`; the failure of (4.20) and (4.21)
gives `MNp < x^{0.775}` and `Np/M < x^{0.1}`; case (i), `f_k` in Lemma 12 by (4.9) with
`M < x^{0.46}`, `g_k` in Theorem 4; `e''_k`, `h` prime and `h, np < x^{0.375}`. Lemma 14, `h_k`
satisfies (4.8), and the three ratios of `j_k`. All MATCH.
Cosmetic: page 30 says "The case (4.6) of Lemma 12 covers h_k"; (4.6) defines ψ, the case is
(4.8), `lemma14_h_in_48`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma1314

/-- Lemma 13, `N > x^{0.375}`: `L = x/MN < x^{0.225} < x^{8/35}`, Lemma 4's (3.30). -/
theorem lemma13_largeN {m n : ℝ} (hm : 0.4 ≤ m) (hn : 0.375 < n) :
    1 - m - n < 0.225 ∧ (0.225 : ℝ) < 8 / 35 := by
  constructor <;> [linarith; norm_num]

/-- (4.20) with `Nh ≥ x^{0.46}`: `p ≪ x^{0.14}`, `M ≤ Nh`, `Nh/M ≤ x^{0.1}`. Here
`p = 1 - m - (n + h)`. -/
theorem lemma13_420 {m n h p : ℝ} (hm : 0.4 ≤ m) (hm' : m ≤ 0.46) (hsum : m + n + h + p = 1)
    (hNh : 0.46 ≤ n + h) (h420 : 0.9 - 2 * m ≤ p) :
    p ≤ 0.14 ∧ m ≤ n + h ∧ n + h - m ≤ 0.1 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Both (4.20) and (4.21) fail: the lower half of (4.21) holds automatically, so
`x/MNp > x^{0.225}`, `MNp < x^{0.775}`; and `Np/M < x^{0.075} < x^{0.1}`. -/
theorem lemma13_fail {m n p : ℝ} (hm : 0.4 ≤ m) (hn : n ≤ 0.375) (hp : p < 0.9 - 2 * m) :
    0.9 - 2 * m ≤ 1 - m - n - p ∧ ((1 - m - n - p ≤ 0.225 → False) → m + n + p < 0.775) ∧
      n + p - m < 0.1 := by
  refine ⟨by linarith, fun h => by by_contra hc; exact h (by linarith), by linarith⟩

/-- Case (i), `x^{0.45}/M ≤ p < x^{0.9}/M²`: for `f_k`, `np < 2x^{0.775}/M < 2x^{0.375}`,
in exponents `0.775 - m ≤ 0.375`; for `g_k`, `Mp ≥ x^{0.45}`, `q(Mp)² ≤ p³M² ≤ x^{2.7}M^{-4} ≤ x^{1.1}`,
`mp/nl ≤ x^{0.1}`, `nl/mp < x^{0.1}`, `q < x^{0.1}`. -/
theorem lemma13_case_i {m p q : ℝ} (hm : 0.4 ≤ m) (hp0 : 0.45 - m ≤ p) (hp1 : p < 0.9 - 2 * m)
    (hq0 : 0 < q) (hq : q < p) :
    0.775 - m ≤ 0.375 ∧ 0.45 ≤ m + p ∧ q + 2 * (m + p) ≤ 3 * p + 2 * m ∧
      3 * p + 2 * m ≤ 2.7 - 4 * m ∧ 2.7 - 4 * m ≤ 1.1 ∧
      2 * (m + p) + q - 1 ≤ 0.1 ∧ 1 - 2 * (m + p) - q < 0.1 ∧ q < 0.1 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- `e''_k`, `p > x^{0.225}`: `mp³ > x` so `h < p²` is prime; `h ≤ x^{0.375}`; `np ≤ x^{0.375}`.
With `m + n + p + h = 1` and `h ≥ p`. -/
theorem lemma13_e2 {m n p h : ℝ} (hm : 0.4 ≤ m) (hn : 0 ≤ n) (hp : 0.225 < p) (hph : p ≤ h)
    (hsum : m + n + p + h = 1) :
    1 < m + 3 * p ∧ h < 2 * p ∧ h ≤ 0.375 ∧ n + p ≤ 0.375 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 14: `h_k` satisfies (4.8), `max(0.45, m) + max(0.225, n) ≤ 0.775`, from (4.22)
`0.46 < m ≤ 0.5`, `m + n ≤ 0.775`. The page cites "(4.6)", which is the definition of ψ. -/
theorem lemma14_h_in_48 {m n : ℝ} (hm : 0.46 < m) (hm' : m ≤ 0.5) (hmn : m + n ≤ 0.775) :
    max 0.45 m + max 0.225 n ≤ 0.775 := by
  rw [max_eq_right (by linarith)]
  rcases le_total n 0.225 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-- Lemma 14, `j_k` with `w ≤ p < z`, `zM² ≤ x^{1.1}`: `p < x^{0.18}`, `m/nh < x^{0.1}`,
`nh/m < x^{0.1}`, with `m + n + p + h = 1`. -/
theorem lemma14_j {m n p h z : ℝ} (hm : 0.46 < m) (hz : z + 2 * m ≤ 1.1) (hp : p < z)
    (hp0 : 0 ≤ p) (hsum : m + n + p + h = 1) :
    p < 0.18 ∧ m - (n + h) < 0.1 ∧ n + h - m < 0.1 := by
  refine ⟨by linarith, by linarith, by linarith⟩

end LeanLab.BHP1997.Lemma1314
