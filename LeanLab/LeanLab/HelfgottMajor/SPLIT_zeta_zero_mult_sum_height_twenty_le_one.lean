import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short_level_one
import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Split of `zeta_zero_mult_sum_height_twenty_le_one`

The zeros of the Riemann zeta function with `0 < Re < 1` and `0 ≤ Im ≤ 20`. The classical
picture, Gram, Note sur les zéros de la fonction ζ(s) de Riemann, Acta Math. 27 1903, and
Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918, is that there
is exactly one, the simple zero `1/2 + 14.134725...i`, and that the next one is at height
`21.022`. This file cuts that picture into its four separate facts:

* the real segment, proved: `ζ(σ)` is real and negative for `0 < σ < 1`, the argument of the lab
  theorem `LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg`, unit U-5111, repeated here from the
  ported StrongPNT formula `ζ(s) = 1 + 1/(s - 1) - s ∫₁^∞ {u} u^{-s-1} du`, Apache-2.0, the
  PrimeNumberTheoremAnd contributors, to keep the import light;
* LEAF, zero free below the first zero: no zero with `0 < Im < 14.134`;
* LEAF, zero free between the first and second zero: no zero with `14.135 < Im ≤ 20`;
* LEAF, the first zero is simple and alone in its box: the zeros with `14.134 ≤ Im ≤ 14.135`
  have multiplicity sum at most `1`.

The assembly is proved. Each leaf is a separate rigorous computation, a zero free rectangle by the
argument principle or a sign change of the Hardy function together with a local count.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology MeasureTheory

/-- Zeta is real and negative on the real segment `(0, 1)`. The proof of the lab theorem
`LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg`, from the ported formula `ZetaAltFormula`,
no input. -/
lemma riemannZeta_real_neg_G1 {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).re < 0 := by
  have hre : 0 < (σ : ℂ).re := by simpa using h0
  have hne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [ZetaAltFormula hre hne, riemannZeta1]
  have hint : (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-(σ : ℂ) - 1)) =
      ((∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans zero_lt_one hu)
    rw [show (-(σ : ℂ) - 1) = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hu0]
    push_cast; ring
  have hnn : 0 ≤ ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu ↦
      mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hu)) _)
  rw [hint]
  set I := ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-σ - 1)
  have e : (1 + 1 / ((σ : ℂ) - 1) - (σ : ℂ) * (I : ℂ)) =
      ((1 + 1 / (σ - 1) - σ * I : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]
  have hσ1 : σ - 1 < 0 := by linarith
  have : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
    have : σ - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [this]
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg h0 hσ1
  nlinarith

/-- Zeta has no zero on the real segment `(0, 1)`, from `riemannZeta_real_neg_G1`, no input. -/
lemma riemannZeta_ne_zero_real_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im = 0) :
    riemannZeta ρ ≠ 0 := by
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hρ]
  intro h
  have := riemannZeta_real_neg_G1 h0 h1
  rw [h] at this
  simp at this

/-- LEAF: zeta has no zero in the critical strip below the first zero. HARD, CITED. Gram, Acta
Math. 27 1903, and Backlund, Acta Math. 41 1918, footnote on the last page: the zeros with
`0 < t < 200` are the 79 zeros on the critical line that he separates, the least at height
`14.134725`. Stated for `0 < Im < 14.134`. -/
theorem riemannZeta_ne_zero_below_first_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 0 < ρ.im) (him : ρ.im < 14.134) :
    riemannZeta ρ ≠ 0 := by
  sorry

/-- LEAF: zeta has no zero in the critical strip between the first and second zero, up to
height `20`. HARD, CITED. Backlund, Acta Math. 41 1918, footnote on the last page, with Gram's
table, Acta Math. 27 1903: after `14.134725` the next zero is at height `21.022040`. Stated for
`14.135 < Im ≤ 20`. -/
theorem riemannZeta_ne_zero_first_gap {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 14.135 < ρ.im) (him : ρ.im ≤ 20) :
    riemannZeta ρ ≠ 0 := by
  sorry

/-- LEAF: the first zero of zeta is simple and the only zero in its box. HARD, CITED. Gram, Acta
Math. 27 1903, and Backlund, Acta Math. 41 1918: the only zero with `0 < Re < 1` and
`14.134 ≤ Im ≤ 14.135` is `1/2 + 14.134725...i`, and it is simple. Stated for every finite set of
zeros in that box: their multiplicity sum is at most `1`. -/
theorem zeta_first_zero_box_mult_sum_le_one (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 14.134 ≤ ρ.im ∧ ρ.im ≤ 14.135) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  sorry

/-- Split of `zeta_zero_mult_sum_height_twenty_le_one`, same statement: every zero in the range
lies in the box of the first zero, by the real segment and the two zero free leaves, and the box
leaf bounds the sum. -/
theorem zeta_zero_mult_sum_height_twenty_le_one_split (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ 20) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  apply zeta_first_zero_box_mult_sum_le_one S
  intro ρ hρ
  obtain ⟨hz, h0, h1, him0, him20⟩ := hS ρ hρ
  refine ⟨hz, h0, h1, ?_, ?_⟩
  · by_contra hlt
    replace hlt := lt_of_not_ge hlt
    rcases him0.lt_or_eq with hpos | heq
    · exact riemannZeta_ne_zero_below_first_zero h0 h1 hpos hlt hz
    · exact riemannZeta_ne_zero_real_strip h0 h1 heq.symm hz
  · by_contra hgt
    replace hgt := lt_of_not_ge hgt
    exact riemannZeta_ne_zero_first_gap h0 h1 hgt him20 hz

end LeanLab.HelfgottMajor.ZeroCount1623
