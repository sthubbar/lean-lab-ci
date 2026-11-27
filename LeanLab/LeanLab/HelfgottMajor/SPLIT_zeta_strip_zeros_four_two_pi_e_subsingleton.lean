import LeanLab.HelfgottMajor.Feed1122ZetaAboveFourCard
import LeanLab.HelfgottMajor.SPLIT_zeta_first_zero_box_mult_sum_le_one

/-!
# Reduction of `zeta_strip_zeros_four_two_pi_e_subsingleton` to the zero leaves of
`ZeroCount1623`, burst-20261127 S2

The HARD leaf `Feed1122ZetaAboveFourCard.zeta_strip_zeros_four_two_pi_e_subsingleton` asks that
the zeros of `ζ` in the open strip with ordinate in `(4, 2πe]`, `2πe < 17.13`, form a set with
at most one element. The lab carries the classical inputs as leaves of `ZeroCount1623`:

* `backlund_zeros_on_line_below_200`, Backlund, Acta Math. 41 1918: such a zero lies on
  `Re s = 1/2`;
* `riemannZeta_critical_line_ne_zero_below_first_zero` and
  `riemannZeta_critical_line_ne_zero_first_gap`, Gram, Acta Math. 27 1903: on the line there is
  no zero with `0 < t < 14.134` or `14.135 < t ≤ 20`;
* `zeta_first_zero_line_unique`, Gram 1903 and Backlund 1918: two line zeros with ordinates in
  `[14.134, 14.135]` coincide.

So the leaf follows with no new sorry: `zeta_strip_zeros_four_two_pi_e_subsingleton_of_leaves`.
The zero is the one the source uses, Helfgott arXiv 1305.2897v4 Section 4.6 page 56, with
Platt's verification [Pla11].

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitZetaStripZerosFourTwoPiESubsingleton
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

/-- `2πe < 20`, from `π < 3.15` and `e < 2.7182818286`. -/
lemma two_pi_e_lt_twenty' : 2 * Real.pi * Real.exp 1 < 20 := by
  have hp := Real.pi_lt_d2
  have he := Real.exp_one_lt_d9
  have hp0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  nlinarith

/-- A strip zero with ordinate in `(4, 2πe]` is `1/2 + it` with `t ∈ [14.134, 14.135]`, from
Backlund's line leaf and Gram's two line leaves. -/
lemma strip_zero_four_two_pi_e_on_line {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (h4 : 4 < ρ.im) (hT : ρ.im ≤ 2 * Real.pi * Real.exp 1) :
    ρ.re = 1 / 2 ∧ 14.134 ≤ ρ.im ∧ ρ.im ≤ 14.135 := by
  have h20 : ρ.im ≤ 20 := hT.trans two_pi_e_lt_twenty'.le
  have hre := backlund_zeros_on_line_below_200 hz h0 h1 (by linarith) (by linarith)
  have hρ := eq_half_add_im_mul_I hre
  refine ⟨hre, ?_, ?_⟩
  · by_contra ha
    exact riemannZeta_critical_line_ne_zero_below_first_zero (by linarith) (not_le.mp ha)
      (hρ ▸ hz)
  · by_contra hb
    exact riemannZeta_critical_line_ne_zero_first_gap (not_le.mp hb) h20 (hρ ▸ hz)

/-- `Feed1122ZetaAboveFourCard.zeta_strip_zeros_four_two_pi_e_subsingleton`, exactly its
statement, from the `ZeroCount1623` leaves of Backlund and Gram and the uniqueness leaf. -/
theorem zeta_strip_zeros_four_two_pi_e_subsingleton_of_leaves :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 4 < ρ.im ∧
      ρ.im ≤ 2 * Real.pi * Real.exp 1}.Subsingleton := by
  rintro ρ ⟨hz, h0, h1, h4, hT⟩ ρ' ⟨hz', h0', h1', h4', hT'⟩
  obtain ⟨hre, ha, hb⟩ := strip_zero_four_two_pi_e_on_line hz h0 h1 h4 hT
  obtain ⟨hre', ha', hb'⟩ := strip_zero_four_two_pi_e_on_line hz' h0' h1' h4' hT'
  have hρ := eq_half_add_im_mul_I hre
  have hρ' := eq_half_add_im_mul_I hre'
  have him := zeta_first_zero_line_unique ha hb ha' hb' (hρ ▸ hz) (hρ' ▸ hz')
  apply Complex.ext
  · rw [hre, hre']
  · exact him

end LeanLab.HelfgottMajor.SplitZetaStripZerosFourTwoPiESubsingleton

#print axioms LeanLab.HelfgottMajor.SplitZetaStripZerosFourTwoPiESubsingleton.two_pi_e_lt_twenty'
#print axioms LeanLab.HelfgottMajor.SplitZetaStripZerosFourTwoPiESubsingleton.strip_zero_four_two_pi_e_on_line
#print axioms LeanLab.HelfgottMajor.SplitZetaStripZerosFourTwoPiESubsingleton.zeta_strip_zeros_four_two_pi_e_subsingleton_of_leaves
