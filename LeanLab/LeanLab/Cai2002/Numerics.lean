/-
P0044, Cai 2002: the arithmetic of Section 4 and the parameter checks, all elementary.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves it.
-/
import Mathlib
import LeanLab.Cai2002.Statements

namespace LeanLab.Cai2002

/-- Final step, p. 604, with the constant 6.8085 as printed there:
`12.9897 - 18.7347/2 - 6.8085/2 - 0.1564 > 0.01`; the margin is 0.06165. -/
theorem final_margin : (0.01 : ℝ) < 12.9897 - 18.7347 / 2 - 6.8085 / 2 - 0.1564 := by norm_num

/-- The same with 6.8086, the value printed in (4.14). -/
theorem final_margin_414 : (0.01 : ℝ) < 12.9897 - 18.7347 / 2 - 6.8086 / 2 - 0.1564 := by norm_num

/-- The assembly of (4.1) with (4.4), (4.7), (4.14), (4.15): any lower bound for `S` and upper
bounds for `S₁, S₂, S₃` in units `K = C(N) N^θ / log² N > 0` give `S - S₁/2 - S₂/2 - S₃ > 0.01 K`.
The `O(N^{10/11})` error and the `1 + o(1)` factors are not modelled here. -/
theorem assembly (K S S1 S2 S3 : ℝ) (hK : 0 < K) (h44 : 12.9897 * K ≤ S)
    (h47 : S1 ≤ 18.7347 * K) (h414 : S2 ≤ 6.8086 * K) (h415 : S3 ≤ 0.1564 * K) :
    0.01 * K < S - S1 / 2 - S2 / 2 - S3 := by nlinarith

/-- The two Lemma 5 cutoff exponents: `1/11 + 3/3.29 > 1`, used for `ρ₁ = 1 ⇒ v₁ = 3`, and
`4/3.29 > 1`, used for `ρ₁ = 0 ⇒ v₁ = 3`. -/
theorem exponents : (1 : ℝ) < 1 / 11 + 3 / 3.29 ∧ (1 : ℝ) < 4 / 3.29 := by norm_num

/-- Sieve dimensions at `θ = 0.95`: `s = 5.5θ = 5.225 ∈ [4, 6]` for `f` in Lemma 2, and the `F`
argument `5.5θ - 11α` runs over `[5.5θ - 11/3.29, 5.5θ - 1] ⊆ (0, 5]`. -/
theorem sieve_ranges :
    (4 : ℝ) ≤ 5.5 * 0.95 ∧ 5.5 * (0.95 : ℝ) ≤ 6 ∧ 0 < 5.5 * (0.95 : ℝ) - 11 / 3.29 ∧
      5.5 * (0.95 : ℝ) - 1 ≤ 5 ∧ 3 ≤ 5.5 * (0.95 : ℝ) - 1 := by norm_num

/-- Lemma 4 admissibility at `θ = 0.95`, `β = 2/3`, p. 603: `3/5 < θ ≤ 1`, `0 ≤ β < (5θ-3)/2`,
and `λ = θ - 1/2 = 0.45`. -/
theorem lemma4_params :
    (3 / 5 : ℝ) < 0.95 ∧ (0.95 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 2 / 3 ∧ (2 / 3 : ℝ) < (5 * 0.95 - 3) / 2 ∧
      (0.95 : ℝ) - 1 / 2 = 0.45 := by norm_num

/-- The range of `e = p₁p₂ ∈ E`, p. 602: `1/11 + 1/3.29 > 1/3` and `(1 + 1/3.29)/2 < 2/3`, so
`N^{1/3} < e < N^{2/3}` as the paper states. -/
theorem E_range : (1 / 3 : ℝ) < 1 / 11 + 1 / 3.29 ∧ (1 + 1 / 3.29) / 2 < (2 / 3 : ℝ) := by
  norm_num

/-- The upper sieve factor `8/(2θ-1)`, p. 603, at `θ = 0.95`, equals `80/9`. -/
theorem upper_factor : (8 : ℝ) / (2 * 0.95 - 1) = 80 / 9 := by norm_num

end LeanLab.Cai2002
