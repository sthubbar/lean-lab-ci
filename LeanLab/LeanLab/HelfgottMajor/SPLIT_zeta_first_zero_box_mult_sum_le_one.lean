import LeanLab.HelfgottMajor.SPLIT_riemannZeta_zero_free_low

/-!
# Split of `zeta_first_zero_box_mult_sum_le_one`

The leaf says that the zeros of zeta with `0 < Re < 1` and `14.134 ≤ Im ≤ 14.135` have
multiplicity sum at most `1`: the first zero `1/2 + 14.134725...i` of Gram, Acta Math. 27 1903,
is alone in its box and simple, Backlund, Acta Math. 41 1918. This file cuts it into its three
separate facts:

* every zero in the box lies on the critical line, the existing Backlund LEAF
  `backlund_zeros_on_line_below_200` of `SPLIT_riemannZeta_zero_free_low.lean`;
* LEAF, at most one zero on the line in the box: `ζ(1/2 + it) = ζ(1/2 + it') = 0` with
  `t, t'` in `[14.134, 14.135]` forces `t = t'`;
* LEAF, the zero on the line in the box is simple: its analytic order is at most `1`.

The assembly is proved: the finite set has at most one element, and that element has order at
most `1`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex

/-- LEAF: Gram, Acta Math. 27 1903, and Backlund, Acta Math. 41 1918, the first zero on the
critical line is isolated in its box. MEDIUM, CITED, a one variable interval computation of the
Hardy function, for instance its strict monotonicity on `[14.134, 14.135]`: two zeros
`1/2 + it` and `1/2 + it'` of zeta with `t, t'` in `[14.134, 14.135]` have `t = t'`. -/
theorem zeta_first_zero_line_unique {t t' : ℝ} (ht0 : 14.134 ≤ t) (ht1 : t ≤ 14.135)
    (ht0' : 14.134 ≤ t') (ht1' : t' ≤ 14.135) (hz : riemannZeta (1 / 2 + t * I) = 0)
    (hz' : riemannZeta (1 / 2 + t' * I) = 0) : t = t' := by
  sorry

/-- LEAF: Backlund, Acta Math. 41 1918, the first zero of zeta is simple. MEDIUM, CITED, a one
variable interval computation, for instance a nonzero derivative of the Hardy function on
`[14.134, 14.135]`: a zero `1/2 + it` with `t` in `[14.134, 14.135]` has analytic order at most
`1`. -/
theorem zeta_first_zero_line_simple {t : ℝ} (ht0 : 14.134 ≤ t) (ht1 : t ≤ 14.135)
    (hz : riemannZeta (1 / 2 + t * I) = 0) :
    analyticOrderNatAt riemannZeta (1 / 2 + t * I) ≤ 1 := by
  sorry

/-- Split of `zeta_first_zero_box_mult_sum_le_one`, same statement, from the Backlund line LEAF
and the two line LEAFs above. -/
theorem zeta_first_zero_box_mult_sum_le_one_split (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 14.134 ≤ ρ.im ∧ ρ.im ≤ 14.135) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  have hline : ∀ ρ ∈ S, ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, him0, him1⟩ := hS ρ hρ
    exact eq_half_add_im_mul_I
      (backlund_zeros_on_line_below_200 hz h0 h1 (by linarith) (by linarith))
  have hord : ∀ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, him0, him1⟩ := hS ρ hρ
    have he := hline ρ hρ
    rw [he] at hz ⊢
    exact_mod_cast zeta_first_zero_line_simple him0 him1 hz
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨hza, -, -, ha0, ha1⟩ := hS a ha
    obtain ⟨hzb, -, -, hb0, hb1⟩ := hS b hb
    have hea := hline a ha
    have heb := hline b hb
    rw [hea] at hza
    rw [heb] at hzb
    have hab := zeta_first_zero_line_unique ha0 ha1 hb0 hb1 hza hzb
    rw [hea, heb, hab]
  calc ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ ∑ _ρ ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum hord
    _ = (S.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.zeta_first_zero_box_mult_sum_le_one_split
