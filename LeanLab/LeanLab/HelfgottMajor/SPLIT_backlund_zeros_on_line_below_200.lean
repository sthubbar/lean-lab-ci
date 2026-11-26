import LeanLab.HelfgottMajor.SPLIT_riemannZeta_zero_free_low

/-!
# Split of `backlund_zeros_on_line_below_200`

Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918: every zero of
zeta with `0 < Im < 200` lies on the critical line. The zeros off the line come in pairs
`ρ, 1 - conj ρ` with the same imaginary part, by the functional equation together with
`ζ (conj s) = conj (ζ s)`; this file proves that reflection from Mathlib's
`riemannZeta_one_sub` and `riemannZeta_conj`, so only the right half of the strip is left:

* proved: `riemannZeta_reflect_zero`, a zero `ρ` with `0 < Re ρ < 1` gives the zero `1 - conj ρ`;
* LEAF: no zero with `1/2 < Re < 1` and `0 < Im < 200`, the content of Backlund's count;
* proved: the assembly, a zero left of the line reflects to one right of it.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex
open scoped ComplexConjugate

/-- LEAF: Backlund, Acta Math. 41 1918, footnote on the last page, the Riemann hypothesis up to
height 200, right half of the strip. HARD, CITED: zeta has no zero with `1/2 < Re < 1` and
`0 < Im < 200`. -/
theorem backlund_no_zero_right_of_line_below_200 {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 0 < ρ.im) (him : ρ.im < 200) :
    riemannZeta ρ ≠ 0 := by
  sorry

/-- Reflection of a zero in the critical strip: if `ζ ρ = 0` and `0 < Re ρ < 1` then
`ζ (1 - conj ρ) = 0`. From the functional equation `riemannZeta_one_sub` at `s = conj ρ` and
`riemannZeta_conj`. Proved, no input. -/
lemma riemannZeta_reflect_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : riemannZeta (1 - conj ρ) = 0 := by
  have hs : ∀ n : ℕ, conj ρ ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : conj ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [riemannZeta_one_sub hs hs', riemannZeta_conj, hz, map_zero, mul_zero]

/-- Split of `backlund_zeros_on_line_below_200`, same statement, from the right half LEAF and
the proved reflection. -/
theorem backlund_zeros_on_line_below_200_split {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him0 : 0 < ρ.im) (him : ρ.im < 200) :
    ρ.re = 1 / 2 := by
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hr := riemannZeta_reflect_zero hz h0 h1
    have hre : (1 - conj ρ).re = 1 - ρ.re := by simp
    have him' : (1 - conj ρ).im = ρ.im := by simp
    exact backlund_no_zero_right_of_line_below_200 (by rw [hre]; linarith)
      (by rw [hre]; linarith) (by rw [him']; exact him0) (by rw [him']; exact him) hr
  · exact heq
  · exact absurd hz (backlund_no_zero_right_of_line_below_200 hgt h1 him0 him)

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.riemannZeta_reflect_zero
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.backlund_zeros_on_line_below_200_split
