import Mathlib
import LeanLab.HelfgottMajor.IntegralCells680

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
  have c0 := IntegralCells680.cell_bound 0 0.035 0.81148 0.09219
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.81148) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.035 0.07 0.81311 0.0921094
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.81311) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.07 0.105 0.81582 0.0913876
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.81582) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.105 0.14 0.81961 0.0900743
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.81961) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 0.035)
    (hc.intervalIntegrable 0.035 0.07)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 0.07)
    (hc.intervalIntegrable 0.07 0.105)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 0.105)
    (hc.intervalIntegrable 0.105 0.14)
  linarith [h1, h2, h3]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.14, 0.28]: ∫ g ≤ 0.333;
the true value is 0.3277. Method: the midpoint rule (b - a) g((a+b)/2), an upper bound because g is concave on [0, 0.288], with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_01 :
    ∫ τ in (0.14 : ℝ)..0.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  have c0 := IntegralCells680.cell_bound 0.14 0.14875 0.82072 0.0218615
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82072) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.14875 0.1575 0.8219 0.0217208
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.8219) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.1575 0.16625 0.82314 0.021574
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82314) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.16625 0.175 0.82445 0.0214219
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82445) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 0.175 0.18375 0.82583 0.0212649
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82583) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 0.18375 0.1925 0.82727 0.0211031
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82727) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 0.1925 0.20125 0.82878 0.0209373
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.82878) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 0.20125 0.21 0.83035 0.0207674
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83035) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 0.21 0.21875 0.83198 0.020594
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83198) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 0.21875 0.2275 0.83368 0.0204178
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83368) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 0.2275 0.23625 0.83544 0.0202387
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83544) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 0.23625 0.245 0.83726 0.0200573
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83726) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 0.245 0.25375 0.83915 0.0198743
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.83915) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 0.25375 0.2625 0.8411 0.0196896
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.8411) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 0.2625 0.27125 0.84311 0.0195036
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.84311) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 0.27125 0.28 0.84519 0.0193171
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.84519) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.14875)
    (hc.intervalIntegrable 0.14875 0.1575)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.1575)
    (hc.intervalIntegrable 0.1575 0.16625)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.16625)
    (hc.intervalIntegrable 0.16625 0.175)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.175)
    (hc.intervalIntegrable 0.175 0.18375)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.18375)
    (hc.intervalIntegrable 0.18375 0.1925)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.1925)
    (hc.intervalIntegrable 0.1925 0.20125)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.20125)
    (hc.intervalIntegrable 0.20125 0.21)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.21)
    (hc.intervalIntegrable 0.21 0.21875)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.21875)
    (hc.intervalIntegrable 0.21875 0.2275)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.2275)
    (hc.intervalIntegrable 0.2275 0.23625)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.23625)
    (hc.intervalIntegrable 0.23625 0.245)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.245)
    (hc.intervalIntegrable 0.245 0.25375)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.25375)
    (hc.intervalIntegrable 0.25375 0.2625)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.2625)
    (hc.intervalIntegrable 0.2625 0.27125)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.14 0.27125)
    (hc.intervalIntegrable 0.27125 0.28)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.28, 0.29]: ∫ g ≤ 0.026;
the true value is 0.0216. Method: the left rectangle (b - a) g(a), an upper bound because g is decreasing on [0, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_02 :
    ∫ τ in (0.28 : ℝ)..0.29, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.026 := by
  have c0 := IntegralCells680.cell_bound 0.28 0.29 0.84763 0.0218781
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.84763) 12))
    (by norm_num)
  linarith


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.29, 0.45]: ∫ g ≤ 0.319;
the true value is 0.3135. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_03 :
    ∫ τ in (0.29 : ℝ)..0.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.319 := by
  have c0 := IntegralCells680.cell_bound 0.29 0.3 0.85016 0.0216335
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.85016) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.3 0.31 0.85276 0.0213883
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.85276) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.31 0.32 0.85544 0.0211436
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.85544) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.32 0.33 0.8582 0.0208998
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.8582) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 0.33 0.34 0.86104 0.0206573
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.86104) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 0.34 0.35 0.86395 0.0204161
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.86395) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 0.35 0.36 0.86694 0.0201768
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.86694) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 0.36 0.37 0.87 0.0199395
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.87) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 0.37 0.38 0.87314 0.0197047
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.87314) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 0.38 0.39 0.87635 0.0194724
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.87635) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 0.39 0.4 0.87963 0.0192427
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.87963) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 0.4 0.41 0.88299 0.0190164
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.88299) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 0.41 0.42 0.88641 0.0187927
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.88641) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 0.42 0.43 0.88991 0.0185727
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.88991) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 0.43 0.44 0.89348 0.0183561
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.89348) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 0.44 0.45 0.89711 0.0181427
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.89711) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.3)
    (hc.intervalIntegrable 0.3 0.31)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.31)
    (hc.intervalIntegrable 0.31 0.32)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.32)
    (hc.intervalIntegrable 0.32 0.33)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.33)
    (hc.intervalIntegrable 0.33 0.34)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.34)
    (hc.intervalIntegrable 0.34 0.35)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.35)
    (hc.intervalIntegrable 0.35 0.36)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.36)
    (hc.intervalIntegrable 0.36 0.37)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.37)
    (hc.intervalIntegrable 0.37 0.38)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.38)
    (hc.intervalIntegrable 0.38 0.39)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.39)
    (hc.intervalIntegrable 0.39 0.4)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.4)
    (hc.intervalIntegrable 0.4 0.41)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.41)
    (hc.intervalIntegrable 0.41 0.42)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.42)
    (hc.intervalIntegrable 0.42 0.43)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.43)
    (hc.intervalIntegrable 0.43 0.44)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.29 0.44)
    (hc.intervalIntegrable 0.44 0.45)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.45, 0.65]: ∫ g ≤ 0.326;
the true value is 0.3191. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_04 :
    ∫ τ in (0.45 : ℝ)..0.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.326 := by
  have c0 := IntegralCells680.cell_bound 0.45 0.4625 0.90175 0.0224628
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.90175) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.4625 0.475 0.9065 0.022142
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.9065) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.475 0.4875 0.91135 0.0218281
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.91135) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.4875 0.5 0.9163 0.0215215
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.9163) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 0.5 0.5125 0.92135 0.0212222
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.92135) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 0.5125 0.525 0.92649 0.0209299
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.92649) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 0.525 0.5375 0.93174 0.0206455
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.93174) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 0.5375 0.55 0.93708 0.0203681
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.93708) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 0.55 0.5625 0.94251 0.0200979
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.94251) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 0.5625 0.575 0.94804 0.0198352
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.94804) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 0.575 0.5875 0.95365 0.0195791
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.95365) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 0.5875 0.6 0.95936 0.0193305
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.95936) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 0.6 0.6125 0.96515 0.0190885
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.96515) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 0.6125 0.625 0.97102 0.0188529
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.97102) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 0.625 0.6375 0.97698 0.0186242
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.97698) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 0.6375 0.65 0.98302 0.0184019
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.98302) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.4625)
    (hc.intervalIntegrable 0.4625 0.475)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.475)
    (hc.intervalIntegrable 0.475 0.4875)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.4875)
    (hc.intervalIntegrable 0.4875 0.5)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.5)
    (hc.intervalIntegrable 0.5 0.5125)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.5125)
    (hc.intervalIntegrable 0.5125 0.525)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.525)
    (hc.intervalIntegrable 0.525 0.5375)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.5375)
    (hc.intervalIntegrable 0.5375 0.55)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.55)
    (hc.intervalIntegrable 0.55 0.5625)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.5625)
    (hc.intervalIntegrable 0.5625 0.575)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.575)
    (hc.intervalIntegrable 0.575 0.5875)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.5875)
    (hc.intervalIntegrable 0.5875 0.6)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.6)
    (hc.intervalIntegrable 0.6 0.6125)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.6125)
    (hc.intervalIntegrable 0.6125 0.625)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.625)
    (hc.intervalIntegrable 0.625 0.6375)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.45 0.6375)
    (hc.intervalIntegrable 0.6375 0.65)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.65, 0.9]: ∫ g ≤ 0.332;
the true value is 0.3240. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_05 :
    ∫ τ in (0.65 : ℝ)..0.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.332 := by
  have c0 := IntegralCells680.cell_bound 0.65 0.6578125 0.98684 0.0113134
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.98684) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.6578125 0.665625 0.99068 0.011231
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.99068) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.665625 0.6734375 0.99456 0.0111503
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.99456) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.6734375 0.68125 0.99847 0.011071
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.99847) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 0.68125 0.6890625 1.0024 0.0109929
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0024) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 0.6890625 0.696875 1.00637 0.0109165
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.00637) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 0.696875 0.7046875 1.01036 0.0108413
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.01036) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 0.7046875 0.7125 1.01439 0.0107677
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.01439) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 0.7125 0.7203125 1.01844 0.0106952
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.01844) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 0.7203125 0.728125 1.02252 0.0106241
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.02252) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 0.728125 0.7359375 1.02662 0.0105542
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.02662) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 0.7359375 0.74375 1.03075 0.0104855
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.03075) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 0.74375 0.7515625 1.03491 0.0104182
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.03491) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 0.7515625 0.759375 1.0391 0.0103522
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0391) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 0.759375 0.7671875 1.04331 0.0102872
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.04331) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 0.7671875 0.775 1.04754 0.0102233
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.04754) 12))
    (by norm_num)
  have c16 := IntegralCells680.cell_bound 0.775 0.7828125 1.0518 0.0101606
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0518) 12))
    (by norm_num)
  have c17 := IntegralCells680.cell_bound 0.7828125 0.790625 1.05609 0.0100992
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.05609) 12))
    (by norm_num)
  have c18 := IntegralCells680.cell_bound 0.790625 0.7984375 1.0604 0.0100388
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0604) 12))
    (by norm_num)
  have c19 := IntegralCells680.cell_bound 0.7984375 0.80625 1.06473 0.0099793
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.06473) 12))
    (by norm_num)
  have c20 := IntegralCells680.cell_bound 0.80625 0.8140625 1.06908 0.0099209
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.06908) 12))
    (by norm_num)
  have c21 := IntegralCells680.cell_bound 0.8140625 0.821875 1.07346 0.0098636
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.07346) 12))
    (by norm_num)
  have c22 := IntegralCells680.cell_bound 0.821875 0.8296875 1.07786 0.0098073
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.07786) 12))
    (by norm_num)
  have c23 := IntegralCells680.cell_bound 0.8296875 0.8375 1.08229 0.0097521
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.08229) 12))
    (by norm_num)
  have c24 := IntegralCells680.cell_bound 0.8375 0.8453125 1.08673 0.0096977
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.08673) 12))
    (by norm_num)
  have c25 := IntegralCells680.cell_bound 0.8453125 0.853125 1.0912 0.0096444
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.0912) 12))
    (by norm_num)
  have c26 := IntegralCells680.cell_bound 0.853125 0.8609375 1.09568 0.0095918
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.09568) 12))
    (by norm_num)
  have c27 := IntegralCells680.cell_bound 0.8609375 0.86875 1.10019 0.0095403
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.10019) 12))
    (by norm_num)
  have c28 := IntegralCells680.cell_bound 0.86875 0.8765625 1.10472 0.0094896
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.10472) 12))
    (by norm_num)
  have c29 := IntegralCells680.cell_bound 0.8765625 0.884375 1.10927 0.0094398
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.10927) 12))
    (by norm_num)
  have c30 := IntegralCells680.cell_bound 0.884375 0.8921875 1.11383 0.0093908
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.11383) 12))
    (by norm_num)
  have c31 := IntegralCells680.cell_bound 0.8921875 0.9 1.11842 0.0093427
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.11842) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.6578125)
    (hc.intervalIntegrable 0.6578125 0.665625)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.665625)
    (hc.intervalIntegrable 0.665625 0.6734375)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.6734375)
    (hc.intervalIntegrable 0.6734375 0.68125)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.68125)
    (hc.intervalIntegrable 0.68125 0.6890625)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.6890625)
    (hc.intervalIntegrable 0.6890625 0.696875)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.696875)
    (hc.intervalIntegrable 0.696875 0.7046875)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7046875)
    (hc.intervalIntegrable 0.7046875 0.7125)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7125)
    (hc.intervalIntegrable 0.7125 0.7203125)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7203125)
    (hc.intervalIntegrable 0.7203125 0.728125)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.728125)
    (hc.intervalIntegrable 0.728125 0.7359375)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7359375)
    (hc.intervalIntegrable 0.7359375 0.74375)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.74375)
    (hc.intervalIntegrable 0.74375 0.7515625)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7515625)
    (hc.intervalIntegrable 0.7515625 0.759375)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.759375)
    (hc.intervalIntegrable 0.759375 0.7671875)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7671875)
    (hc.intervalIntegrable 0.7671875 0.775)
  have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.775)
    (hc.intervalIntegrable 0.775 0.7828125)
  have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7828125)
    (hc.intervalIntegrable 0.7828125 0.790625)
  have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.790625)
    (hc.intervalIntegrable 0.790625 0.7984375)
  have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.7984375)
    (hc.intervalIntegrable 0.7984375 0.80625)
  have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.80625)
    (hc.intervalIntegrable 0.80625 0.8140625)
  have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8140625)
    (hc.intervalIntegrable 0.8140625 0.821875)
  have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.821875)
    (hc.intervalIntegrable 0.821875 0.8296875)
  have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8296875)
    (hc.intervalIntegrable 0.8296875 0.8375)
  have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8375)
    (hc.intervalIntegrable 0.8375 0.8453125)
  have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8453125)
    (hc.intervalIntegrable 0.8453125 0.853125)
  have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.853125)
    (hc.intervalIntegrable 0.853125 0.8609375)
  have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8609375)
    (hc.intervalIntegrable 0.8609375 0.86875)
  have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.86875)
    (hc.intervalIntegrable 0.86875 0.8765625)
  have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8765625)
    (hc.intervalIntegrable 0.8765625 0.884375)
  have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.884375)
    (hc.intervalIntegrable 0.884375 0.8921875)
  have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.65 0.8921875)
    (hc.intervalIntegrable 0.8921875 0.9)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [0.9, 1.2]: ∫ g ≤ 0.333;
the true value is 0.3258. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_06 :
    ∫ τ in (0.9 : ℝ)..1.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.333 := by
  have c0 := IntegralCells680.cell_bound 0.9 0.909375 1.12395 0.0111728
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.12395) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 0.909375 0.91875 1.1295 0.0111057
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.1295) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 0.91875 0.928125 1.13508 0.01104
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.13508) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 0.928125 0.9375 1.14069 0.0109757
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.14069) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 0.9375 0.946875 1.14632 0.0109126
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.14632) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 0.946875 0.95625 1.15197 0.0108506
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.15197) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 0.95625 0.965625 1.15765 0.01079
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.15765) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 0.965625 0.975 1.16335 0.0107305
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.16335) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 0.975 0.984375 1.16907 0.010672
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.16907) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 0.984375 0.99375 1.17482 0.0106149
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.17482) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 0.99375 1.003125 1.18058 0.0105586
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.18058) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 1.003125 1.0125 1.18637 0.0105035
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.18637) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 1.0125 1.021875 1.19218 0.0104495
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.19218) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 1.021875 1.03125 1.198 0.0103962
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.198) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 1.03125 1.040625 1.20385 0.0103442
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.20385) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 1.040625 1.05 1.20971 0.0102929
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.20971) 12))
    (by norm_num)
  have c16 := IntegralCells680.cell_bound 1.05 1.059375 1.21559 0.0102426
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.21559) 12))
    (by norm_num)
  have c17 := IntegralCells680.cell_bound 1.059375 1.06875 1.22149 0.0101932
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.22149) 12))
    (by norm_num)
  have c18 := IntegralCells680.cell_bound 1.06875 1.078125 1.22741 0.0101448
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.22741) 12))
    (by norm_num)
  have c19 := IntegralCells680.cell_bound 1.078125 1.0875 1.23334 0.0100971
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.23334) 12))
    (by norm_num)
  have c20 := IntegralCells680.cell_bound 1.0875 1.096875 1.23929 0.0100503
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.23929) 12))
    (by norm_num)
  have c21 := IntegralCells680.cell_bound 1.096875 1.10625 1.24525 0.0100042
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.24525) 12))
    (by norm_num)
  have c22 := IntegralCells680.cell_bound 1.10625 1.115625 1.25123 0.0099589
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.25123) 12))
    (by norm_num)
  have c23 := IntegralCells680.cell_bound 1.115625 1.125 1.25722 0.0099144
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.25722) 12))
    (by norm_num)
  have c24 := IntegralCells680.cell_bound 1.125 1.134375 1.26323 0.0098707
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.26323) 12))
    (by norm_num)
  have c25 := IntegralCells680.cell_bound 1.134375 1.14375 1.26925 0.0098276
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.26925) 12))
    (by norm_num)
  have c26 := IntegralCells680.cell_bound 1.14375 1.153125 1.27528 0.0097852
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.27528) 12))
    (by norm_num)
  have c27 := IntegralCells680.cell_bound 1.153125 1.1625 1.28133 0.0097436
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.28133) 12))
    (by norm_num)
  have c28 := IntegralCells680.cell_bound 1.1625 1.171875 1.28739 0.0097027
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.28739) 12))
    (by norm_num)
  have c29 := IntegralCells680.cell_bound 1.171875 1.18125 1.29346 0.0096624
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.29346) 12))
    (by norm_num)
  have c30 := IntegralCells680.cell_bound 1.18125 1.190625 1.29954 0.0096226
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.29954) 12))
    (by norm_num)
  have c31 := IntegralCells680.cell_bound 1.190625 1.2 1.30563 0.0095835
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.30563) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.909375)
    (hc.intervalIntegrable 0.909375 0.91875)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.91875)
    (hc.intervalIntegrable 0.91875 0.928125)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.928125)
    (hc.intervalIntegrable 0.928125 0.9375)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.9375)
    (hc.intervalIntegrable 0.9375 0.946875)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.946875)
    (hc.intervalIntegrable 0.946875 0.95625)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.95625)
    (hc.intervalIntegrable 0.95625 0.965625)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.965625)
    (hc.intervalIntegrable 0.965625 0.975)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.975)
    (hc.intervalIntegrable 0.975 0.984375)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.984375)
    (hc.intervalIntegrable 0.984375 0.99375)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 0.99375)
    (hc.intervalIntegrable 0.99375 1.003125)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.003125)
    (hc.intervalIntegrable 1.003125 1.0125)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.0125)
    (hc.intervalIntegrable 1.0125 1.021875)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.021875)
    (hc.intervalIntegrable 1.021875 1.03125)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.03125)
    (hc.intervalIntegrable 1.03125 1.040625)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.040625)
    (hc.intervalIntegrable 1.040625 1.05)
  have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.05)
    (hc.intervalIntegrable 1.05 1.059375)
  have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.059375)
    (hc.intervalIntegrable 1.059375 1.06875)
  have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.06875)
    (hc.intervalIntegrable 1.06875 1.078125)
  have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.078125)
    (hc.intervalIntegrable 1.078125 1.0875)
  have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.0875)
    (hc.intervalIntegrable 1.0875 1.096875)
  have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.096875)
    (hc.intervalIntegrable 1.096875 1.10625)
  have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.10625)
    (hc.intervalIntegrable 1.10625 1.115625)
  have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.115625)
    (hc.intervalIntegrable 1.115625 1.125)
  have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.125)
    (hc.intervalIntegrable 1.125 1.134375)
  have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.134375)
    (hc.intervalIntegrable 1.134375 1.14375)
  have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.14375)
    (hc.intervalIntegrable 1.14375 1.153125)
  have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.153125)
    (hc.intervalIntegrable 1.153125 1.1625)
  have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.1625)
    (hc.intervalIntegrable 1.1625 1.171875)
  have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.171875)
    (hc.intervalIntegrable 1.171875 1.18125)
  have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.18125)
    (hc.intervalIntegrable 1.18125 1.190625)
  have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0.9 1.190625)
    (hc.intervalIntegrable 1.190625 1.2)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]


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
