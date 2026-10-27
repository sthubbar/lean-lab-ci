/-
P0035 Pintz, Ruzsa 2020, On Linnik's approximation to Goldbach's problem II, read from papers/P0035.pdf,
the open copy real.mtak.hu/124682, unit U-5048. Theorem 1: every large even N is p + p' + 8 powers of 2.

PROVED: `c20_lt`, (4.7), `C₀ R₀ (C* - 1) + log 2 / 2 < 4.0826` for `C₀ ≤ 0.66017`, `R₀ < 1.94`,
`C* = 3.9171`; `c3_lt`, (6.11), `A(4) + 4.0826 · 0.789401⁶ < 0.992` for `A(4) < 0.004`;
`cauchy_conv`, the Cauchy step of (6.10), `∑_{m+n=N} s(m) s(n) ≤ ∑_{n≤N} s(n)²`;
`positivity_of_C3`, the end of the proof, (6.9) with (6.10): the main term `2 L^{2k} N` beats the rest
when `C₃ < 1`. C₀ = 0.6601618 by numerics/pr2_check.py; R₀, C*, c₁ and A(4) are cited, Pintz-Ruzsa 2003,
Chen 1978, Khalfalah-Pintz 2006. Binary Goldbach is OPEN; this is the Linnik approximation.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Linnik.PR2020
open Finset Real

/-- (4.7): `C₂₀ < 4.0826`. -/
theorem c20_lt {C0 R0 : ℝ} (hC0 : 0 ≤ C0) (hC0' : C0 ≤ 0.66017) (hR0 : 0 ≤ R0) (hR0' : R0 < 1.94) :
    C0 * R0 * (3.9171 - 1) + log 2 / 2 < 4.0826 := by
  have hl := log_two_lt_d9
  have : C0 * R0 ≤ 0.66017 * 1.94 := mul_le_mul hC0' hR0'.le hR0 (by norm_num)
  norm_num at hl ⊢; nlinarith

/-- (6.11): `C₃(4) < 0.992`. -/
theorem c3_lt {A : ℝ} (hA : A < 0.004) : A + 4.0826 * (0.789401 : ℝ) ^ 6 < 0.992 := by
  norm_num; linarith

/-- The Cauchy step of (6.10). -/
theorem cauchy_conv (s : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ range (N + 1), s m * s (N - m) ≤ ∑ n ∈ range (N + 1), s n ^ 2 := by
  have hrefl : ∑ m ∈ range (N + 1), s (N - m) ^ 2 = ∑ n ∈ range (N + 1), s n ^ 2 := by
    have := sum_range_reflect (fun n => s n ^ 2) (N + 1)
    simpa [Nat.add_sub_cancel] using this
  -- the elementary form: 2 a b ≤ a² + b², summed, then reflect
  have h2 : ∀ m ∈ range (N + 1), s m * s (N - m) ≤ (s m ^ 2 + s (N - m) ^ 2) / 2 := fun m _ => by
    nlinarith [sq_nonneg (s m - s (N - m))]
  calc ∑ m ∈ range (N + 1), s m * s (N - m) ≤ ∑ m ∈ range (N + 1), (s m ^ 2 + s (N - m) ^ 2) / 2 :=
        sum_le_sum h2
    _ = (∑ n ∈ range (N + 1), s n ^ 2 + ∑ m ∈ range (N + 1), s (N - m) ^ 2) / 2 := by
        rw [← sum_div, sum_add_distrib]
    _ = ∑ n ∈ range (N + 1), s n ^ 2 := by rw [hrefl]; ring

/-- The end of the proof: if `r'' = 2 L^{2k} N + E + X` with `|E| ≤ η L^{2k} N`, `|X| ≤ 2 N L^{2k} C₃`,
`C₃ < 1` and `η < 2 (1 - C₃)`, then `r'' > 0`. -/
theorem positivity_of_C3 {r M E X C3 η : ℝ} (hM : 0 < M) (hr : r = 2 * M + E + X)
    (hE : |E| ≤ η * M) (hX : |X| ≤ 2 * M * C3) (hη : η < 2 * (1 - C3)) : 0 < r := by
  rw [abs_le] at hE hX
  nlinarith

end LeanLab.Linnik.PR2020
