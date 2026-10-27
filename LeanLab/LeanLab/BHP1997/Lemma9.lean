/-
P0069 Baker, Harman, Pintz 1997, Lemma 9, pages 22 and 23, read from the page images
papers/P0069-original.pdf. Unit U-5155, CLOUD 20261019T0213Z-cloud14.

PROVED, the elementary steps of the proof: `horiz`, on `σ ∈ [0, c]` the horizontal segments'
`(qT)^{c-σ}N^σT^{-1}`, in logarithms `(c - σ)k + σn - τ`, is at most its larger endpoint value,
which at `c = 1/2` gives `q^{1/2}T^{-1/2} + N^{1/2}T^{-1}`; `pow4_sum`, `(a + b + c + d)⁴ ≤ 64(a⁴ + b⁴ + c⁴ + d⁴)`,
which takes (3.36) to fourth powers; `fourth_powers`, `(q^{1/2}T^{-1/2})⁴ = q²/T²`,
`(N^{1/2}/T)⁴ = N²/T⁴`, `(N^{1/2}/(1 + |t|))⁴ = N²/(1 + |t|)⁴`, the terms of the statement.
All MATCH. Perron's formula, Hölder's inequality, the spacing sum and Lemma 7 are not formalized here.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma9

theorem horiz {k n σ c τ : ℝ} (h0 : 0 ≤ σ) (hc : σ ≤ c) :
    (c - σ) * k + σ * n - τ ≤ max (c * k - τ) (c * n - τ) := by
  rcases le_total k n with h | h
  · have : (c - σ) * k + σ * n ≤ c * n := by nlinarith
    exact le_max_of_le_right (by linarith)
  · have : (c - σ) * k + σ * n ≤ c * k := by nlinarith
    exact le_max_of_le_left (by linarith)

theorem pow4_sum (a b c d : ℝ) : (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have h1 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d)]
  have h2 : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2),
      sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2)]
  have h3 : ((a + b + c + d) ^ 2) ^ 2 ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (a + b + c + d) ^ 4 = ((a + b + c + d) ^ 2) ^ 2 := by ring
    _ ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 := h3
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by ring
    _ ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by linarith

theorem fourth_powers {q T N t : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T) (hN : 0 ≤ N) :
    (Real.sqrt q / Real.sqrt T) ^ 4 = q ^ 2 / T ^ 2 ∧ (Real.sqrt N / T) ^ 4 = N ^ 2 / T ^ 4 ∧
      (Real.sqrt N / (1 + |t|)) ^ 4 = N ^ 2 / (1 + |t|) ^ 4 := by
  have e : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ 4 = x ^ 2 := fun x hx => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hx]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pow, e q hq, e T hT]
  · rw [div_pow, e N hN]
  · rw [div_pow, e N hN]

end LeanLab.BHP1997.Lemma9
