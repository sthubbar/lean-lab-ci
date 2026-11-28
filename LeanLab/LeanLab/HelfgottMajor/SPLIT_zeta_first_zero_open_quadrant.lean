import LeanLab.HelfgottMajor.ZetaRealSegment1123
import LeanLab.HelfgottMajor.SPLIT_riemannZeta_zero_free_low

/-!
# Reduction of `zeta_first_zero_open_quadrant` to the zero leaves of `ZeroCount1623`,
burst-20261127 S2

The MEDIUM leaf `ZetaRealSegment1123.zeta_first_zero_open_quadrant`, book Part I section 3.7.3.3
page 86, cited there to Gram 1903 and Edwards 1974 section 6.1, asks that a zero of `ζ` with
`1/2 ≤ Re < 1` and `Im > 0` have `Im > 14.13`. The lab carries the classical inputs as leaves of
`ZeroCount1623` in `SPLIT_riemannZeta_zero_free_low.lean`: Backlund, Acta Math. 41 1918, every
strip zero below height `200` is on the line, and Gram, Acta Math. 27 1903, no line zero with
`0 < t < 14.134`. They give the leaf with no new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitZetaFirstZeroOpenQuadrant
open Complex
open scoped ComplexConjugate
open LeanLab.HelfgottMajor.ZeroCount1623

/-- `ZetaRealSegment1123.zeta_first_zero_open_quadrant`, exactly its statement, from the
`ZeroCount1623` leaves `backlund_zeros_on_line_below_200` and
`riemannZeta_critical_line_ne_zero_below_first_zero`. -/
theorem zeta_first_zero_open_quadrant_of_leaves {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 1 / 2 ≤ ρ.re) (h1 : ρ.re < 1) (him : 0 < ρ.im) : (14.13 : ℝ) < ρ.im := by
  by_contra h
  rw [not_lt] at h
  exact riemannZeta_ne_zero_below_first_zero_split (by linarith) h1 him (by linarith) hz

/-- `ZetaFirstZero1123.zeta_first_zero_quadrant`, exactly its statement, from the reduction above
and the proved real segment `ZetaRealSegment1123.zeta_ne_zero_of_real`; the same assembly as
`ZetaRealSegment1123.zeta_first_zero_quadrant_split`. -/
theorem zeta_first_zero_quadrant_of_leaves {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 1 / 2 ≤ ρ.re) (h1 : ρ.re < 1) (him : 0 ≤ ρ.im) : (14.13 : ℝ) < ρ.im := by
  rcases him.lt_or_eq with hlt | heq
  · exact zeta_first_zero_open_quadrant_of_leaves hz h0 h1 hlt
  · exfalso
    have hρ : ρ = (ρ.re : ℂ) := by
      apply Complex.ext <;> simp [← heq]
    exact LeanLab.HelfgottMajor.ZetaRealSegment1123.zeta_ne_zero_of_real (by linarith) h1
      (hρ ▸ hz)

/-- `BookZeroSplit1122.zeta_first_zero`, exactly its statement, book Part I section 3.7.3.3
page 86, from `zeta_first_zero_quadrant_of_leaves` by conjugation and `s ↦ 1 - s`, the same
assembly as `ZetaFirstZero1123.zeta_first_zero_split` with the proved symmetries
`ZetaFirstZero1123.zeta_zero_conj` and `ZetaFirstZero1123.zeta_zero_one_sub`. -/
theorem zeta_first_zero_of_leaves {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : (14.13 : ℝ) < |ρ.im| := by
  have right : ∀ {σ : ℂ}, riemannZeta σ = 0 → 1 / 2 ≤ σ.re → σ.re < 1 →
      (14.13 : ℝ) < |σ.im| := by
    intro σ hz h0 h1
    rcases le_or_gt 0 σ.im with h | h
    · rw [abs_of_nonneg h]
      exact zeta_first_zero_quadrant_of_leaves hz h0 h1 h
    · have hc := zeta_first_zero_quadrant_of_leaves
        (LeanLab.HelfgottMajor.ZetaFirstZero1123.zeta_zero_conj hz) (by rwa [conj_re])
        (by rwa [conj_re]) (by rw [conj_im]; linarith)
      rw [conj_im] at hc
      rw [abs_of_neg h]
      exact hc
  rcases le_or_gt (1 / 2) ρ.re with h | h
  · exact right hz h h1
  · have hz' := LeanLab.HelfgottMajor.ZetaFirstZero1123.zeta_zero_one_sub hz h0 h1
    have hr := right hz' (by rw [sub_re, one_re]; linarith) (by rw [sub_re, one_re]; linarith)
    rw [sub_im, one_im, zero_sub, abs_neg] at hr
    exact hr

example : type_of% @zeta_first_zero_of_leaves =
    type_of% @LeanLab.HelfgottMajor.BookZeroSplit1122.zeta_first_zero := rfl

end LeanLab.HelfgottMajor.SplitZetaFirstZeroOpenQuadrant

#print axioms LeanLab.HelfgottMajor.SplitZetaFirstZeroOpenQuadrant.zeta_first_zero_open_quadrant_of_leaves
#print axioms LeanLab.HelfgottMajor.SplitZetaFirstZeroOpenQuadrant.zeta_first_zero_quadrant_of_leaves
#print axioms LeanLab.HelfgottMajor.SplitZetaFirstZeroOpenQuadrant.zeta_first_zero_of_leaves
