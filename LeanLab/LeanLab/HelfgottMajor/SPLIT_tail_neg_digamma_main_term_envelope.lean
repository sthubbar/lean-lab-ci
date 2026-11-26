import Mathlib

/-!
Route burst S4, burst-20261124, unit S4-05. Split of the LEAF
`Decomp457b.tail_neg_digamma_main_term_envelope` of
`HelfgottMajor/SPLIT_principal_log_weight_tail_neg_digamma_envelope.lean`, the elementary
envelope closing the gamma factor step of P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897, page 34 display 4.10, on the line of real part minus one half.

The target is sharp only near height two: its margin is `0.00040` at `|t| = 2` and `0.38` at
`|t| = 3`, per the doc comment of the target. The cut separates the two regimes, so that the
four digit work on the argument of `w = 5/2 + it` and on the logarithm stays on a compact
interval and the unbounded range keeps a margin of more than one third.
No new definition. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Complex

/-- LEAF: the envelope of P0014 page 34 display 4.10 on the compact range `2 ≤ |t| ≤ 3`,
where it is sharp, margin `0.00040` at `|t| = 2`. Same expression as the target: the Stirling
main term at `w = 5/2 + it` minus the three recurrence terms, plus the budget `2/9375`, is at
most `log |t| + 3/2`. Class HARD: needs certified enclosures of `arctan (2t/5)` and of the
logarithms to about four digits, for instance by interval subdivision of `[2, 3]`. -/
theorem tail_neg_digamma_main_term_envelope_low (t : ℝ) (h2 : 2 ≤ |t|) (h3 : |t| ≤ 3) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  sorry

/-- LEAF: the envelope of P0014 page 34 display 4.10 on the unbounded range `3 ≤ |t|`, where
the margin is at least about `0.38`. Same expression as the target. Class MEDIUM: the
imaginary part is at most `π/2` plus `O(1/|t|)` and the real part is `log |t| + O(1/t^2)`,
so crude bounds `|arg w| ≤ π/2` and `log |w| ≤ log |t| + 25/(8 t^2)` with
`sqrt (a^2 + b^2) ≤ a + b^2/(2a)` should suffice. -/
theorem tail_neg_digamma_main_term_envelope_high (t : ℝ) (h3 : 3 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  sorry

/-- The target `tail_neg_digamma_main_term_envelope`, exact statement, from the two range
LEAFs. -/
theorem tail_neg_digamma_main_term_envelope_of_leaves (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  rcases le_total |t| 3 with h | h
  · exact tail_neg_digamma_main_term_envelope_low t ht h
  · exact tail_neg_digamma_main_term_envelope_high t h

end LeanLab.HelfgottMajor.Decomp457b
