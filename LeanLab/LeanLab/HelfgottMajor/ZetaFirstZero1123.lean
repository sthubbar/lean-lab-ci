import LeanLab.HelfgottMajor.BookZeroSplit1122
import Mathlib

/-!
# Split of `BookZeroSplit1122.zeta_first_zero`, burst-20261122, session S116

Book Part I, section 3.7.3.3, page 86: the first non-trivial zero of zeta has imaginary part
14.13472..., cited there to Gra03 and Edw74 section 6.1. The leaf of `BookZeroSplit1122` asks for
every zero in the open strip, with either sign of the imaginary part. The zeros of zeta in the
strip are symmetric under conjugation and under s to 1 - s, so the computation is needed only in
the quarter 1/2 at most Re s below 1, Im s at least 0. This file PROVES both reductions from
Mathlib, `riemannZeta_conj` and the functional equation `riemannZeta_one_sub`, and leaves the
quarter as the single LEAF `zeta_first_zero_quadrant`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZetaFirstZero1123
open Complex
open scoped ComplexConjugate

/-- LEAF: book Part I, section 3.7.3.3, page 86, the first non-trivial zero of zeta has
imaginary part 14.13472..., cited to Gra03 and Edw74 section 6.1, restricted to the quarter
1/2 at most Re s below 1 and Im s at least 0, which by `zeta_first_zero_split` is all that is
needed. The real segment Im s = 0 is included. Stated with the weaker constant 14.13.
Class MEDIUM: a finite certified computation of zeta on a rectangle of height 14.13. -/
theorem zeta_first_zero_quadrant {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 ≤ ρ.re)
    (h1 : ρ.re < 1) (him : 0 ≤ ρ.im) : (14.13 : ℝ) < ρ.im := by
  sorry

/-- Zeros of zeta are closed under conjugation. Proved from Mathlib `riemannZeta_conj`. -/
theorem zeta_zero_conj {ρ : ℂ} (hz : riemannZeta ρ = 0) : riemannZeta (conj ρ) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-- Zeros of zeta in the open strip are closed under s to 1 - s. Proved from the functional
equation, Mathlib `riemannZeta_one_sub`: zeta of 1 - s is a multiple of zeta of s. -/
theorem zeta_zero_one_sub {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 := by
  have hs : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hs' : ρ ≠ 1 := by
    intro h
    rw [h, one_re] at h1
    exact lt_irrefl _ h1
  rw [riemannZeta_one_sub hs hs', hz, mul_zero]

/-- The right half of the strip, either sign of Im, from the quadrant LEAF by conjugation. -/
theorem zeta_zero_right_half {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 ≤ ρ.re)
    (h1 : ρ.re < 1) : (14.13 : ℝ) < |ρ.im| := by
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h]
    exact zeta_first_zero_quadrant hz h0 h1 h
  · have hc := zeta_first_zero_quadrant (zeta_zero_conj hz) (by rwa [conj_re])
      (by rwa [conj_re]) (by rw [conj_im]; linarith)
    rw [conj_im] at hc
    rw [abs_of_neg h]
    exact hc

/-- ASSEMBLY. Exactly the statement of `BookZeroSplit1122.zeta_first_zero`, PROVED from the
quadrant LEAF by the two symmetries. CONDITIONAL ON `zeta_first_zero_quadrant`. -/
theorem zeta_first_zero_split {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : (14.13 : ℝ) < |ρ.im| := by
  rcases le_or_gt (1 / 2) ρ.re with h | h
  · exact zeta_zero_right_half hz h h1
  · have hz' := zeta_zero_one_sub hz h0 h1
    have hr := zeta_zero_right_half hz' (by rw [sub_re, one_re]; linarith)
      (by rw [sub_re, one_re]; linarith)
    rw [sub_im, one_im, zero_sub, abs_neg] at hr
    exact hr

example : type_of% @zeta_first_zero_split = type_of% @BookZeroSplit1122.zeta_first_zero := rfl

end LeanLab.HelfgottMajor.ZetaFirstZero1123
