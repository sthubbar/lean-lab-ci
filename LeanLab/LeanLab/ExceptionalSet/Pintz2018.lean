/-
P0016 Pintz 2018, A new explicit formula in the additive theory of primes with applications II,
arXiv 1804.09084v2, read from the LaTeX source, unit U-5046. Section 9, the proof of
`E(X) < X^{0.72}`: the closing arithmetic of Cases 1 to 6 and 7, and Case 8 in full.

PROVED: `s922`, (9.22) to (9.26), `S⁻ + Δ₁ + Δ₂ < 0.9832`; `s930`, (9.30) `< 0.99991`;
`exp_neg_le_quad`, `e^{-y} ≤ 1 - y + y²/2` for `y ≥ 0`; `case8_core`, (9.36) to (9.37),
`e^{-7λ} + 5λ < 1` for `0 < λ ≤ 0.04`; `case8`, the full (9.36),
`e^{-50λ/7} + 2.87 · 10.4 · λ^{11/7} < 1` for `0 < λ ≤ 0.04`. The inputs 0.622, 0.0722, 6.805 and
the rest are the paper's, recomputed in gen/pintz_check.py and gen/pintz_lemma6.py, numerical
certificates, not theorems. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Pintz2018
open Real

/-- (9.22) plus the surpluses (9.24) and (9.26): below 0.9832. -/
theorem s922 :
    (0.622 : ℝ) ^ 2 + 0.0722 * (2 * 0.622 + 6.805) + (0.0826 - 0.0722) * (1.244 + 2 * 0.0826) +
      (0.0751 - 0.0722) * (2 * 0.0751) < 0.9832 := by
  norm_num

/-- (9.30), Case 7. -/
theorem s930 : (0.86671 : ℝ) ^ 2 + 0.0715 * (2 * 0.86671 + 1.74516) < 0.99991 := by
  norm_num

/-- `e^{-y} ≤ 1 - y + y²/2` for `y ≥ 0`. -/
theorem exp_neg_le_quad {y : ℝ} (hy : 0 ≤ y) : exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h3 : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 ≤ exp y := by
    have := Real.sum_le_exp_of_nonneg hy 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this ⊢; linarith
  have hpos : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 := by positivity
  rw [exp_neg, inv_le_iff_one_le_mul₀' (exp_pos y)]
  have hA : 0 ≤ 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
  calc (1 : ℝ) ≤ (1 + y + y ^ 2 / 2 + y ^ 3 / 6) * (1 - y + y ^ 2 / 2) := by
        nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5]
    _ ≤ exp y * (1 - y + y ^ 2 / 2) := mul_le_mul_of_nonneg_right h3 hA

/-- (9.36) to (9.37): `e^{-7λ} + 5λ < 1` for `0 < λ ≤ 0.04`. -/
theorem case8_core {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 0.04) : exp (-7 * l) + 5 * l < 1 := by
  have := exp_neg_le_quad (y := 7 * l) (by linarith)
  rw [show -(7 * l) = -7 * l by ring] at this
  nlinarith

/-- The full (9.36): `e^{-50λ/7} + 2.87 · 10.4 · λ^{11/7} < 1` for `0 < λ ≤ 0.04`. -/
theorem case8 {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 0.04) :
    exp (-(50 / 7) * l) + 2.87 * 10.4 * l ^ (11 / 7 : ℝ) < 1 := by
  have he : exp (-(50 / 7) * l) ≤ exp (-7 * l) := exp_le_exp.mpr (by nlinarith)
  -- l^{4/7} ≤ 0.1675, since (l^{4/7})^7 = l^4 ≤ 0.04^4 < 0.1675^7
  have hq : l ^ (4 / 7 : ℝ) ≤ 0.1675 := by
    have hp : 0 ≤ l ^ (4 / 7 : ℝ) := rpow_nonneg h0.le _
    have h7 : (l ^ (4 / 7 : ℝ)) ^ (7 : ℕ) = l ^ 4 := by
      rw [← rpow_natCast, ← rpow_mul h0.le]; norm_num
    have hl4 : l ^ 4 ≤ (0.04 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h1 4
    by_contra hc
    push Not at hc
    have : (0.1675 : ℝ) ^ 7 < (l ^ (4 / 7 : ℝ)) ^ 7 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [h7] at this
    norm_num at this hl4; linarith
  have hsplit : l ^ (11 / 7 : ℝ) = l * l ^ (4 / 7 : ℝ) := by
    rw [show (11 / 7 : ℝ) = 1 + 4 / 7 by norm_num, rpow_add h0, rpow_one]
  have hb : 2.87 * 10.4 * l ^ (11 / 7 : ℝ) ≤ 5 * l := by
    rw [hsplit]; nlinarith
  have := case8_core h0 h1
  linarith

end LeanLab.ExceptionalSet.Pintz2018
