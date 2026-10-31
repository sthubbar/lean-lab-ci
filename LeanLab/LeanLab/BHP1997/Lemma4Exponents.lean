/-
P0069 Baker, Harman, Pintz 1997, Lemma 4, pages 18 and 19, read from the page images
papers/P0069-original.pdf. Unit U-5064, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log X`; `k` for `qT`, `m, n, l` for `M, N, L`, `m + n + l = 1`;
(3.23) `k ≤ 0.45 - ε/2`, (3.30) `m, n ≤ 0.46 + ε/2`, `l ≤ 8/35`.
PROVED: every interpolation of Cases 2 and 3 has weights summing to 1, the σ terms cancel and
the exponents are the printed ones; `min(0, y) ≤ (3/10) y` and `min(a, b) ≤ (a + b)/2`; and
the four final bounds hold with margins `3ε/8`, `ε/2`, at least 0.003, and `ε/24`. The bound
`(qT)^{1/2} X^{1/12} M^{5/12} ≪ X^{1/2}` is exactly tight at `ε = 0`: 0.46 in (3.30) is
the largest `M` exponent it allows. All MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma4

/-! ### Case 2: `M^{c(σ₁)} < qT`, `N^{c(σ₂)} < qT` -/

/-- First product, weights `5/16, 1/16, 5/16, 1/16, 1/4`: `(qT)^{3/4} (MN)^{1/16} L^{1/2}`. -/
theorem case2_first (k m n l s1 s2 s3 : ℝ) :
    5 / 16 * (k + m * (1 - 2 * s1)) + 1 / 16 * (k + m * (4 - 6 * s1)) +
      5 / 16 * (k + n * (1 - 2 * s2)) + 1 / 16 * (k + n * (4 - 6 * s2)) +
      1 / 4 * (l * (4 - 4 * s3)) + m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) =
      3 / 4 * k + (m + n) / 16 + l / 2 ∧
    (5 / 16 + 1 / 16 + 5 / 16 + 1 / 16 + 1 / 4 : ℝ) = 1 := by
  constructor <;> ring

/-- Second product, first option, weights as above with `qT L^{2-4σ₃}`: `qT (MN)^{1/16}`. -/
theorem case2_second_a (k m n l s1 s2 s3 : ℝ) :
    5 / 16 * (k + m * (1 - 2 * s1)) + 1 / 16 * (k + m * (4 - 6 * s1)) +
      5 / 16 * (k + n * (1 - 2 * s2)) + 1 / 16 * (k + n * (4 - 6 * s2)) +
      1 / 4 * (k + l * (2 - 4 * s3)) + m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) =
      k + (m + n) / 16 := by ring

/-- Second option, weights `7/16, 1/48, 7/16, 1/48, 1/12` with `qT L^{8-12σ₃}`:
`qT (MN)^{1/48} L^{1/6}`, that is `qT (MN)^{1/16} L^{1/6} (MN)^{-1/24}`. -/
theorem case2_second_b (k m n l s1 s2 s3 : ℝ) :
    7 / 16 * (k + m * (1 - 2 * s1)) + 1 / 48 * (k + m * (4 - 6 * s1)) +
      7 / 16 * (k + n * (1 - 2 * s2)) + 1 / 48 * (k + n * (4 - 6 * s2)) +
      1 / 12 * (k + l * (8 - 12 * s3)) + m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) =
      k + (m + n) / 16 + (l / 6 - (m + n) / 24) ∧
    (7 / 16 + 1 / 48 + 7 / 16 + 1 / 48 + 1 / 12 : ℝ) = 1 := by
  constructor <;> ring

/-- `min(1, y) ≤ y^{3/10}`, in exponents. -/
theorem min_le_frac (y : ℝ) : min 0 y ≤ 3 / 10 * y := by
  rcases le_total 0 y with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- Case 2, the conclusion: `(qT)^{3/4} X^{1/16} L^{7/16} ≤ (qT)^{3/4} X^{13/80}` and
`qT (MN)^{1/16} (L^{1/6}(MN)^{-1/24})^{3/10} = qT X^{1/20}`, both `≪ X^{1/2}`. -/
theorem case2_final {ε k m n l : ℝ} (hε : 0 < ε) (hsum : m + n + l = 1)
    (hk : k ≤ 0.45 - ε / 2) (hl : l ≤ 8 / 35) (hl0 : 0 ≤ l) :
    3 / 4 * k + (m + n) / 16 + l / 2 ≤ 1 / 2 - 3 * ε / 8 ∧
      k + (m + n) / 16 + 3 / 10 * (l / 6 - (m + n) / 24) = k + 1 / 20 ∧
      k + 1 / 20 ≤ 1 / 2 - ε / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have : m + n = 1 - l := by linarith
    rw [this]; linarith
  · have : m + n = 1 - l := by linarith
    rw [this]; ring_nf
  · linarith

/-! ### Case 3: `M^{c(σ₁)} ≥ qT`, `N^{c(σ₂)} < qT` -/

/-- First product, weights `1/2, 1/8, 1/8, 1/4`: `(qT)^{1/4} M^{1/2} N^{1/8} L^{1/2}`. -/
theorem case3_first (k m n l s1 s2 s3 : ℝ) :
    1 / 2 * (m * (2 - 2 * s1)) + 1 / 8 * (k + n * (1 - 2 * s2)) +
      1 / 8 * (k + n * (4 - 6 * s2)) + 1 / 4 * (l * (4 - 4 * s3)) +
      m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) = k / 4 + m / 2 + n / 8 + l / 2 := by
  ring

/-- Second product, the two options: `(qT)^{1/2} M^{1/2} N^{1/8}` with weights
`1/2, 1/8, 1/8, 1/4`, and `(qT)^{1/2} M^{1/2} N^{1/24} L^{1/6}` with `1/2, 3/8, 1/24, 1/12`. -/
theorem case3_second (k m n l s1 s2 s3 : ℝ) :
    1 / 2 * (m * (2 - 2 * s1)) + 1 / 8 * (k + n * (1 - 2 * s2)) +
      1 / 8 * (k + n * (4 - 6 * s2)) + 1 / 4 * (k + l * (2 - 4 * s3)) +
      m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) = k / 2 + m / 2 + n / 8 ∧
    1 / 2 * (m * (2 - 2 * s1)) + 3 / 8 * (k + n * (1 - 2 * s2)) +
      1 / 24 * (k + n * (4 - 6 * s2)) + 1 / 12 * (k + l * (8 - 12 * s3)) +
      m * (s1 - 1 / 2) + n * (s2 - 1 / 2) + l * (s3 - 1 / 2) = k / 2 + m / 2 + n / 24 + l / 6 ∧
    (1 / 2 + 3 / 8 + 1 / 24 + 1 / 12 : ℝ) = 1 := by
  refine ⟨by ring, by ring, by norm_num⟩

/-- `min(a, b) ≤ (a + b)/2`, used for `min{N^{1/8}, N^{1/24} L^{1/6}} ≤ N^{1/16 + 1/48} L^{1/12}`. -/
theorem min_le_avg (a b : ℝ) : min a b ≤ (a + b) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- Case 3, the conclusion (3.31): `(qT)^{1/4} X^{1/8} (ML)^{3/8}` and
`(qT)^{1/2} X^{1/12} M^{5/12}` are both `≪ X^{1/2}`, for `ε < 0.01`. -/
theorem case3_final {ε k m n l : ℝ} (hε : 0 < ε) (hε1 : ε < 0.01) (hsum : m + n + l = 1)
    (hk : k ≤ 0.45 - ε / 2) (hm : m ≤ 0.46 + ε / 2) (hl : l ≤ 8 / 35) :
    k / 4 + m / 2 + n / 8 + l / 2 = k / 4 + 1 / 8 + 3 / 8 * (m + l) ∧
      k / 4 + 1 / 8 + 3 / 8 * (m + l) < 1 / 2 - 0.003 ∧
      k / 2 + m / 2 + (n / 16 + n / 48) + l / 12 = k / 2 + 1 / 12 + 5 / 12 * m ∧
      k / 2 + 1 / 12 + 5 / 12 * m ≤ 1 / 2 - ε / 24 := by
  have hn : n = 1 - m - l := by linarith
  subst hn
  refine ⟨by ring, by linarith, by ring, by linarith⟩

/-- The `0.46` of (3.30) is sharp for the last bound: at `ε = 0`, `k = 0.45`, `m = 0.46` the
exponent is exactly 1/2. -/
theorem sharp_046 : (0.45 : ℝ) / 2 + 1 / 12 + 5 / 12 * 0.46 = 1 / 2 := by norm_num

end LeanLab.BHP1997.Lemma4
