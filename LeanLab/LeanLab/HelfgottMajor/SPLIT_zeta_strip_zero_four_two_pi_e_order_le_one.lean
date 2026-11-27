import LeanLab.HelfgottMajor.Feed1122ZetaAboveFourOne
import LeanLab.HelfgottMajor.SPLIT_zeta_first_zero_box_mult_sum_le_one

/-!
# Reduction of `zeta_strip_zero_four_two_pi_e_order_le_one` to the zero leaves of
`ZeroCount1623`, burst-20261127 S2

The HARD leaf `Feed1122ZetaAboveFourOne.zeta_strip_zero_four_two_pi_e_order_le_one` asks that a
zero of `ζ` in the open strip with ordinate in `(4, 2πe]`, `2πe < 17.13`, have analytic order at
most one. The lab already carries the classical inputs as separate leaves of `ZeroCount1623`:

* `backlund_zeros_on_line_below_200`, Backlund, Acta Math. 41 1918: every such zero lies on
  `Re s = 1/2`;
* `riemannZeta_critical_line_ne_zero_below_first_zero` and
  `riemannZeta_critical_line_ne_zero_first_gap`, Gram, Acta Math. 27 1903: on the line there is
  no zero with `0 < t < 14.134` or `14.135 < t ≤ 20`;
* `zeta_first_zero_line_simple`, Backlund 1918: a zero `1/2 + it` with `t ∈ [14.134, 14.135]`
  has analytic order at most one.

These four give the leaf, so this file adds no new sorry: the theorem
`zeta_strip_zero_four_two_pi_e_order_le_one_of_leaves` proves exactly its statement from them,
and the window `(1, 4]` parent from them together with the proved Euler Maclaurin range of
`Feed1122ZetaEM4`. The same zero is the one the source uses, Helfgott arXiv 1305.2897v4
Section 4.6 page 56, with Platt's verification [Pla11].

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitZetaStripZeroFourTwoPiEOrder
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

/-- `2πe < 20`, from `π < 3.15` and `e < 2.7182818286`. -/
lemma two_pi_e_lt_twenty : 2 * Real.pi * Real.exp 1 < 20 := by
  have hp := Real.pi_lt_d2
  have he := Real.exp_one_lt_d9
  have hp0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  nlinarith

/-- `Feed1122ZetaAboveFourOne.zeta_strip_zero_four_two_pi_e_order_le_one`, exactly its
statement, from Backlund's line leaf, Gram's two line leaves and the simple first zero leaf. -/
theorem zeta_strip_zero_four_two_pi_e_order_le_one_of_leaves :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 4 < ρ.im →
      ρ.im ≤ 2 * Real.pi * Real.exp 1 → (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  intro ρ hz h0 h1 h4 hT
  have h20 : ρ.im ≤ 20 := hT.trans two_pi_e_lt_twenty.le
  have hre := backlund_zeros_on_line_below_200 hz h0 h1 (by linarith) (by linarith)
  have hρ := eq_half_add_im_mul_I hre
  by_cases ha : ρ.im < 14.134
  · exact absurd (hρ ▸ hz) (riemannZeta_critical_line_ne_zero_below_first_zero (by linarith) ha)
  by_cases hb : 14.135 < ρ.im
  · exact absurd (hρ ▸ hz) (riemannZeta_critical_line_ne_zero_first_gap hb h20)
  have hs := zeta_first_zero_line_simple (not_lt.mp ha) (not_lt.mp hb) (hρ ▸ hz)
  rw [← hρ] at hs
  exact_mod_cast hs

/-- The parent `zeta_strip_zero_above_one_le_two_pi_e_order_le_one`, exactly its statement, from
the proved Euler Maclaurin range `(1, 4]` and the four `ZeroCount1623` leaves. -/
theorem zeta_strip_zero_above_one_le_two_pi_e_order_le_one_of_leaves :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 < ρ.im →
      ρ.im ≤ 2 * Real.pi * Real.exp 1 → (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  intro ρ h0 h1 h2 h3 h4
  by_cases h : ρ.im ≤ 4
  · exact absurd h0
      (LeanLab.HelfgottMajor.Feed1122ZetaEM4.riemannZeta_ne_zero_one_four ρ h1 h2 h3 h)
  · exact zeta_strip_zero_four_two_pi_e_order_le_one_of_leaves ρ h0 h1 h2 (not_le.mp h) h4

end LeanLab.HelfgottMajor.SplitZetaStripZeroFourTwoPiEOrder

#print axioms LeanLab.HelfgottMajor.SplitZetaStripZeroFourTwoPiEOrder.two_pi_e_lt_twenty
#print axioms LeanLab.HelfgottMajor.SplitZetaStripZeroFourTwoPiEOrder.zeta_strip_zero_four_two_pi_e_order_le_one_of_leaves
#print axioms LeanLab.HelfgottMajor.SplitZetaStripZeroFourTwoPiEOrder.zeta_strip_zero_above_one_le_two_pi_e_order_le_one_of_leaves
