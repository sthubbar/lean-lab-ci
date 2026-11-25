/-
Split of `leaf_zeta_quarter_box508` of `LEAF_feed1122_zero_reciprocal508_p2_box` into one
cited leaf, the second order Euler Maclaurin bound for zeta, and a proved arithmetic step.

Source: P0029 page 11 display 3.7, the zeta part of the low zero gap, which rests on the
classical fact that zeta has no zero of small height, Titchmarsh chapter 15. The route used
here is the Euler Maclaurin formula of Titchmarsh section 2.1, carried one step further by
integrating the sawtooth `{x} - 1/2` once: for `Re s > 0`, `s ≠ 1`,
`ζ(s) = 1/(s-1) + 1/2 - s (s+1) ∫_1^∞ P(x) x^{-s-2} dx` with `P` the periodic primitive of
`{x} - 1/2`, so `|P| ≤ 1/8`. That gives the bound of the leaf below; on the quarter box the
main term `1/(s-1) + 1/2 = (s+1)/(2(s-1))` has modulus at least about `0.67` while the error is
at most about `0.27`, which is the proved part.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.LEAF_feed1122_zero_reciprocal508_p2_box

namespace LeanLab.BhowmikGrimmelt2026

open Complex

/-- LEAF: Titchmarsh section 2.1, the Euler Maclaurin formula for zeta with one more
integration by parts, as used for the low zero gap of P0029 page 11 display 3.7: for
`Re s > 0` and `s ≠ 1`, `|ζ(s) - 1/(s-1) - 1/2| ≤ |s| |s+1| / (8 (Re s + 1))`, from
`ζ(s) = 1/(s-1) + 1/2 - s (s+1) ∫_1^∞ P(x) x^{-s-2} dx` with `|P| ≤ 1/8`. Checked numerically
with mpmath at sample points. Class MEDIUM. -/
theorem leaf_zeta_euler_maclaurin2_508 :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      ‖riemannZeta s - (1 / (s - 1) + 1 / 2)‖ ≤ ‖s‖ * ‖s + 1‖ / (8 * (s.re + 1)) := by
  sorry

/-- `leaf_zeta_quarter_box508` from the second order Euler Maclaurin bound. CONDITIONAL ON
`leaf_zeta_euler_maclaurin2_508`. -/
theorem leaf_zeta_quarter_box508_split :
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re < 1 → 0 ≤ s.im → s.im ≤ 1 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3 hz
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hE := leaf_zeta_euler_maclaurin2_508 s (by linarith) hs1
  rw [hz, zero_sub, norm_neg] at hE
  have hmain : 1 / (s - 1) + 1 / 2 = (s + 1) / (2 * (s - 1)) := by
    field_simp; ring
  rw [hmain, norm_div, norm_mul] at hE
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2] at hE
  have hp1 : 0 < ‖s + 1‖ := by
    rw [norm_pos_iff]; intro h
    have := congrArg Complex.re h; simp at this; linarith
  have hm1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsub
  have hden : 0 < 8 * (s.re + 1) := by linarith
  -- from the bound: 4 (re s + 1) ≤ ‖s‖ ‖s - 1‖
  have key : 4 * (s.re + 1) ≤ ‖s‖ * ‖s - 1‖ := by
    rw [div_le_div_iff₀ (by positivity) hden] at hE
    nlinarith [norm_nonneg s]
  have hsq : ‖s‖ ^ 2 ≤ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hsq' : ‖s - 1‖ ^ 2 ≤ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith
  have hprod : (‖s‖ * ‖s - 1‖) ^ 2 ≤ 4 := by
    rw [mul_pow]; nlinarith [sq_nonneg ‖s‖, sq_nonneg ‖s - 1‖]
  nlinarith [norm_nonneg s, norm_nonneg (s - 1)]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_zeta_quarter_box508_split
