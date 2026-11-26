import LeanLab.HelfgottMajor.SPLIT_zeta_zero_mult_sum_height_twenty_le_one

/-!
# Split of the two zero free leaves below height 20

The leaves `riemannZeta_ne_zero_below_first_zero` and `riemannZeta_ne_zero_first_gap` of
`SPLIT_zeta_zero_mult_sum_height_twenty_le_one.lean` say that zeta has no zero in the critical
strip with `0 < Im < 14.134` or with `14.135 < Im ≤ 20`. The classical proof has two separate
parts, and this file cuts each leaf along them:

* Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918, footnote on the
  last page: every zero with `0 < Im < 200` lies on the critical line `Re = 1/2`. This is the
  count `N(200) = 79` by the argument principle against the 79 sign changes of the Hardy function.
  One LEAF, `backlund_zeros_on_line_below_200`.
* Gram, Note sur les zéros de la fonction ζ(s) de Riemann, Acta Math. 27 1903: on the line, the
  first zero is at height `14.134725` and the second at `21.022040`. Two LEAFs, one real variable
  each: `ζ(1/2 + it) ≠ 0` for `0 < t < 14.134` and for `14.135 < t ≤ 20`.

The two old leaves are proved from these three. The line leaves are statements about one real
function of one real variable, the Hardy function up to a nonzero factor, so they are separate
rigorous interval computations, smaller than the strip statements they replace.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex

/-- LEAF: Backlund, Acta Math. 41 1918, footnote on the last page, the Riemann hypothesis up to
height 200. HARD, CITED: every zero of zeta with `0 < Re < 1` and `0 < Im < 200` has real part
`1/2`. -/
theorem backlund_zeros_on_line_below_200 {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him0 : 0 < ρ.im) (him : ρ.im < 200) :
    ρ.re = 1 / 2 := by
  sorry

/-- LEAF: Gram, Acta Math. 27 1903, the first zero on the critical line is at height
`14.134725`. MEDIUM, CITED, a one variable interval computation of the Hardy function: for
`0 < t < 14.134`, `ζ(1/2 + it) ≠ 0`. -/
theorem riemannZeta_critical_line_ne_zero_below_first_zero {t : ℝ} (ht0 : 0 < t)
    (ht : t < 14.134) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- LEAF: Gram, Acta Math. 27 1903, the second zero on the critical line is at height
`21.022040`. MEDIUM, CITED, a one variable interval computation of the Hardy function: for
`14.135 < t ≤ 20`, `ζ(1/2 + it) ≠ 0`. -/
theorem riemannZeta_critical_line_ne_zero_first_gap {t : ℝ} (ht0 : 14.135 < t)
    (ht : t ≤ 20) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- A point of the critical line is `1/2 + it` with `t` its imaginary part. Proved. -/
lemma eq_half_add_im_mul_I {ρ : ℂ} (hre : ρ.re = 1 / 2) : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
  apply Complex.ext <;> simp [hre]

/-- Split of `riemannZeta_ne_zero_below_first_zero`, same statement, from Backlund's line
leaf and Gram's first line leaf. -/
theorem riemannZeta_ne_zero_below_first_zero_split {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 0 < ρ.im) (him : ρ.im < 14.134) :
    riemannZeta ρ ≠ 0 := by
  intro hz
  have hre := backlund_zeros_on_line_below_200 hz h0 h1 him0 (by linarith)
  have hne := riemannZeta_critical_line_ne_zero_below_first_zero him0 him
  rw [← eq_half_add_im_mul_I hre] at hne
  exact hne hz

/-- Split of `riemannZeta_ne_zero_first_gap`, same statement, from Backlund's line leaf and
Gram's second line leaf. -/
theorem riemannZeta_ne_zero_first_gap_split {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 14.135 < ρ.im) (him : ρ.im ≤ 20) :
    riemannZeta ρ ≠ 0 := by
  intro hz
  have hre := backlund_zeros_on_line_below_200 hz h0 h1 (by linarith) (by linarith)
  have hne := riemannZeta_critical_line_ne_zero_first_gap him0 him
  rw [← eq_half_add_im_mul_I hre] at hne
  exact hne hz

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.riemannZeta_ne_zero_below_first_zero_split
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.riemannZeta_ne_zero_first_gap_split
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.eq_half_add_im_mul_I
