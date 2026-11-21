import Mathlib

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part C, the subintervals of [0, 1.2].
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
printed 226.844 after display 4.12. Its only hard part is g(τ) = log(τ² + 9/4)² / (1/4 + τ²),
see `Prep1121VIIntegral`. Each LEAF bounds ∫ g over one subinterval [a, b] by a decimal V that
exceeds the stated quadrature rule by at least 0.004 and the true value by at least 0.0043,
checked with mpmath at 30 digits. The paper's integration used VNODE-LP, footnote 4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIPiecesLow
open Real

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0, 0.14]: ∫ g ≤ 0.368;
the true value is 0.3616. Method: the midpoint rule (b - a) g((a+b)/2), an upper bound because g is concave on [0, 0.288], with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_00 :
    ∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.368 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.14, 0.28]: ∫ g ≤ 0.333;
the true value is 0.3277. Method: the midpoint rule (b - a) g((a+b)/2), an upper bound because g is concave on [0, 0.288], with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_01 :
    ∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.28, 0.29]: ∫ g ≤ 0.026;
the true value is 0.0216. Method: the left rectangle (b - a) g(a), an upper bound because g is decreasing on [0, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_02 :
    ∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.026 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.29, 0.45]: ∫ g ≤ 0.319;
the true value is 0.3135. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_03 :
    ∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.319 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.45, 0.65]: ∫ g ≤ 0.326;
the true value is 0.3191. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_04 :
    ∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.326 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.65, 0.9]: ∫ g ≤ 0.332;
the true value is 0.3240. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_05 :
    ∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.332 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.9, 1.2]: ∫ g ≤ 0.333;
the true value is 0.3258. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_06 :
    ∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  sorry

/-- P0014 page 35: the sum of the subinterval bounds of this file, 2.037. -/
theorem sum_low :
    (∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) ≤ 2.037 := by
  linarith [piece_00, piece_01, piece_02, piece_03, piece_04, piece_05, piece_06]

end LeanLab.HelfgottMajor.Prep1121VIPiecesLow
