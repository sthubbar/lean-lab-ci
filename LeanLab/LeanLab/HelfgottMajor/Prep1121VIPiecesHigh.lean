import Mathlib

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part D, the subintervals of [1.2, 10].
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
printed 226.844 after display 4.12. Its only hard part is g(τ) = log(τ² + 9/4)² / (1/4 + τ²),
see `Prep1121VIIntegral`. Each LEAF bounds ∫ g over one subinterval [a, b] by a decimal V that
exceeds the stated quadrature rule by at least 0.004 and the true value by at least 0.0043,
checked with mpmath at 30 digits. The paper's integration used VNODE-LP, footnote 4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIPiecesHigh
open Real

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [1.2, 1.6]: ∫ g ≤ 0.382;
the true value is 0.3751. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_07 :
    ∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.382 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [1.6, 2.1]: ∫ g ≤ 0.417;
the true value is 0.4109. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_08 :
    ∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.417 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.1, 2.8]: ∫ g ≤ 0.506;
the true value is 0.4995. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_09 :
    ∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.506 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.8, 3.8]: ∫ g ≤ 0.604;
the true value is 0.5970. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_10 :
    ∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.604 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [3.8, 5.2]: ∫ g ≤ 0.675;
the true value is 0.6647. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_11 :
    ∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.675 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [5.2, 7.2]: ∫ g ≤ 0.728;
the true value is 0.7145. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_12 :
    ∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.728 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [7.2, 10]: ∫ g ≤ 0.732;
the true value is 0.7147. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_13 :
    ∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.732 := by
  sorry

/-- P0014 page 35: the sum of the subinterval bounds of this file, 4.044. -/
theorem sum_high :
    (∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) ≤ 4.044 := by
  linarith [piece_07, piece_08, piece_09, piece_10, piece_11, piece_12, piece_13]

end LeanLab.HelfgottMajor.Prep1121VIPiecesHigh
