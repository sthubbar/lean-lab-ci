import LeanLab.HelfgottMajor.Prep1121VIPiecesLow
import LeanLab.HelfgottMajor.Prep1121VIPiecesHigh

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part E.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
∫_ℝ |(1/2) log(τ² + 9/4) + 4.1396 + log π|² / (1/4 + τ²) dτ, printed as at most 226.844.

QUESTION, numerical: footnote 4 says the paper integrated over [-100000, 100000] only. The
full line value is 226.84991, above the printed 226.844. The lab's statement uses 6.01, and
2π · 6.01² = 226.94928, so the full line value still fits, margin 0.0994. This file proves
the full line bound by 2π · 6.01² from leaves.

Route: with ℓ = log(τ² + 9/4), w = 1/(1/4 + τ²) and C = 4.1396 + log π, expand
((1/2)ℓ + C)² w = (1/4) ℓ² w + C ℓ w + C² w. The last two integrals are exact,
∫ w = 2π and ∫ ℓ w = 4π log 2, so only ∫ ℓ² w is numerical: it is twice ∫_0^∞, cut at
0, 0.14, 0.28, 0.29, 0.45, 0.65, 0.9, 1.2, 1.6, 2.1, 2.8, 3.8, 5.2, 7.2, 10 into the
fourteen EASY leaves of `Prep1121VIPiecesLow` and `Prep1121VIPiecesHigh`, plus a tail on
[10, ∞). Total budget 10.878 for ∫_0^∞ ℓ² w, true value 10.73804.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIIntegral
open Real MeasureTheory Set

/-- LEAF: P0014 page 35, the integral after display 4.12, the tail: for τ ≥ 10,
log(τ² + 9/4) ≤ 2 log τ + 9/(4·100) and 1/(1/4 + τ²) ≤ 1/τ², and
∫_X^∞ (2 log τ + e)² / τ² dτ = ((2 log X + e)² + 4(2 log X + e) + 8)/X, which is 4.79260 at
X = 10, e = 0.0225; the true tail is 4.76833. Class MEDIUM: an improper integral with an
explicit antiderivative and a bound on log 10. -/
theorem tail_le :
    ∫ τ in Ioi (10 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 4.797 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12: ∫_0^∞ splits at the nodes of the
fourteen subintervals and the tail at 10. Class MEDIUM: integrability on Ioi 0 of
log(τ² + 9/4)²/(1/4 + τ²), which is O(log² τ / τ²), and
`intervalIntegral.integral_interval_sub_left` style splitting. -/
theorem half_line_split :
    ∫ τ in Ioi (0 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) =
      ((∫ τ in (0 : ℝ)..0.14, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))) +
      ((∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))) +
      ∫ τ in Ioi (10 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) := by
  sorry

/-- LEAF: P0014 page 35: the integrand ℓ² w is even, so its integral over ℝ is twice its
integral over (0, ∞). Class EASY: a Mathlib lookup for even integrands, as
`integral_comp_neg` with `Ioi`/`Iic` splitting. PROVED here by `integral_comp_abs`. -/
theorem full_eq_two_half :
    ∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) =
      2 * ∫ τ in Ioi (0 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) := by
  have h := integral_comp_abs (f := fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
  simp only [sq_abs] at h
  exact h

/-- LEAF: P0014 page 35: expansion of the square, ∫ ((1/2)ℓ + C)² w = (1/4) ∫ ℓ² w +
C ∫ ℓ w + C² ∫ w, for any real C. Class MEDIUM: integrability on ℝ of w, ℓ w and ℓ² w,
then `integral_add` and `integral_mul_left`. -/
theorem expand_square (C : ℝ) :
    ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + C) ^ 2 / (1 / 4 + τ ^ 2) =
      (1 / 4) * (∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
        C * (∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2)) +
        C ^ 2 * (∫ τ : ℝ, 1 / (1 / 4 + τ ^ 2)) := by
  sorry

/-- LEAF: P0014 page 35: ∫_ℝ dτ / (1/4 + τ²) = 2π, the Plancherel weight of the line
re s = -1/2, since |s|² = 1/4 + τ². Class EASY: `integral_univ_inv_one_add_sq` and the
substitution τ = u/2. PROVED here. -/
theorem integral_weight : ∫ τ : ℝ, 1 / (1 / 4 + τ ^ 2) = 2 * π := by
  have h : (fun τ : ℝ => 1 / (1 / 4 + τ ^ 2)) = fun τ => 4 * (1 + (2 * τ) ^ 2)⁻¹ := by
    funext τ
    have : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have : (0 : ℝ) < 1 + (2 * τ) ^ 2 := by positivity
    field_simp
    ring
  rw [h, integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) 2,
    integral_univ_inv_one_add_sq]
  norm_num
  ring

/-- LEAF: P0014 page 35, exact part of the integral: ∫_ℝ log(τ² + b²)/(τ² + a²) dτ =
(2π/a) log(a + b), here a = 1/2, b = 3/2, giving 4π log 2; numerically 8.7103443612.
The paper computes the whole integral numerically; the closed form only shortens the
certified part. Class HARD: Poisson kernel or differentiation in b under the integral. -/
theorem integral_log_weight :
    ∫ τ : ℝ, Real.log (τ ^ 2 + 9 / 4) / (1 / 4 + τ ^ 2) = 4 * π * Real.log 2 := by
  sorry

/-- LEAF: numerical, log π ≤ 1.1449; the true value is 1.1447298858, margin 1.7e-4.
Class EASY: `Real.pi_lt_d6` and π ≤ exp 1.1449 = e · exp 0.1449, with `Real.exp_one_gt_d9`
and a cubic Taylor lower bound for exp 0.1449, or `Real.exp_bound`. PROVED here with
exp 1.1449 = e · exp(0.07245)² and the quadratic Taylor bound. -/
theorem log_pi_le : Real.log π ≤ 1.1449 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.07245)
  have he : Real.exp 1.1449 = Real.exp 1 * (Real.exp 0.07245 * Real.exp 0.07245) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [he]
  have hpi := Real.pi_lt_d6
  have h0 : 0 ≤ Real.exp 0.07245 := (Real.exp_pos _).le
  have h3 : (1.155785 : ℝ) ≤ Real.exp 0.07245 * Real.exp 0.07245 := by nlinarith
  nlinarith

/-- P0014 page 35: ∫_0^∞ log(τ² + 9/4)²/(1/4 + τ²) dτ ≤ 10.878, from the fourteen
subinterval leaves and the tail. -/
theorem half_le : ∫ τ in Ioi (0 : ℝ), Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 10.878 := by
  rw [half_line_split]
  linarith [Prep1121VIPiecesLow.sum_low, Prep1121VIPiecesHigh.sum_high, tail_le]

/-- P0014 page 35, the integral after display 4.12 with the lab's constant 6.01 in place of
the printed √(226.844/(2π)) = 6.00868:
∫_ℝ ((1/2) log(τ² + 9/4) + 4.1396 + log π)² / (1/4 + τ²) dτ ≤ 2π · 6.01². -/
theorem certified_integral :
    ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2) ≤ 2 * π * 6.01 ^ 2 := by
  rw [expand_square, full_eq_two_half, integral_log_weight, integral_weight]
  have hH := half_le
  have hlp := log_pi_le
  have hlp0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpi1 := Real.pi_lt_d6
  have hpi2 := Real.pi_gt_d6
  set C := 4.1396 + Real.log π with hC
  have hC1 : C ≤ 5.2845 := by rw [hC]; linarith
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  have h1 : C * (4 * π * Real.log 2) ≤ 5.2845 * (4 * 3.141593 * 0.6931471808) := by
    have : π * Real.log 2 ≤ 3.141593 * 0.6931471808 :=
      mul_le_mul hpi1.le hl2.le hl20 (by norm_num)
    have h' : 4 * π * Real.log 2 ≤ 4 * 3.141593 * 0.6931471808 := by nlinarith
    have h0 : 0 ≤ 4 * π * Real.log 2 := by positivity
    exact mul_le_mul hC1 h' h0 (by norm_num)
  have h2 : C ^ 2 * (2 * π) ≤ 5.2845 ^ 2 * (2 * 3.141593) := by
    have hsq : C ^ 2 ≤ 5.2845 ^ 2 := pow_le_pow_left₀ hC0 hC1 2
    exact mul_le_mul hsq (by linarith) (by positivity) (by norm_num)
  nlinarith

end LeanLab.HelfgottMajor.Prep1121VIIntegral
