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

/-- P0014 page 35, the integral after display 4.12: g, written in v = τ² + 9/4 as
log(v)²/(v - 2), does not increase on [u, 2u] once u ≥ 16. Used to replace the trapezoid rule
of the LEAF docs by left sums, which need no convexity. Proof: log v ≤ log u + (v - u)/u and
log u ≥ 4 log 2 ≥ 2.77. PROVED here, burst-20261122 S8. -/
theorem f_anti (u v : ℝ) (hu : 16 ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * u) :
    Real.log v ^ 2 / (v - 2) ≤ Real.log u ^ 2 / (u - 2) := by
  have hu0 : 0 < u := by linarith
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hL : 2.77 ≤ Real.log u := by
    have := Real.log_le_log (by norm_num) hu
    linarith [Real.log_two_gt_d9]
  have hlv : Real.log v ≤ Real.log u + (v - u) / u := by
    have h := Real.log_le_sub_one_of_pos (div_pos (show (0:ℝ) < v by linarith) hu0)
    rw [Real.log_div (x := v) (y := u) (by linarith) (by linarith)] at h
    have : v / u - 1 = (v - u) / u := by field_simp
    linarith
  have hlv0 : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  set L := Real.log u with hLdef
  set d := (v - u) / u with hd
  have hd0 : 0 ≤ d := div_nonneg (by linarith) hu0.le
  have hd1 : d ≤ 1 := by rw [hd, div_le_one hu0]; linarith
  have hvd : v = u + d * u := by rw [hd]; field_simp; ring
  have hsq : Real.log v ^ 2 ≤ (L + d) ^ 2 := by
    have : 0 ≤ Real.log v := by linarith
    nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have key : (L + d) ^ 2 * (u - 2) ≤ L ^ 2 * (v - 2) := by
    rw [hvd]
    have hq : 1 ≤ L ^ 2 - 2 * L - d := by nlinarith
    have hb : 0 ≤ u * (L ^ 2 - 2 * L - d) + 4 * L + 2 * d := by
      have := mul_nonneg hu0.le (show 0 ≤ L ^ 2 - 2 * L - d by linarith)
      linarith
    nlinarith [mul_nonneg hd0 hb]
  calc Real.log v ^ 2 * (u - 2) ≤ (L + d) ^ 2 * (u - 2) :=
        mul_le_mul_of_nonneg_right hsq (by linarith)
    _ ≤ L ^ 2 * (v - 2) := key

/-- The integrand g of P0014 page 35 is continuous on ℝ. PROVED here, burst-20261122 S8. -/
theorem g_cont : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) := by
  have h : ∀ τ : ℝ, τ ^ 2 + 9 / 4 ≠ 0 := fun τ => by positivity
  exact Continuous.div (Continuous.pow (Continuous.log (by fun_prop) h) 2) (by fun_prop)
    (fun τ => by positivity)

/-- P0014 page 35, the integral after display 4.12: on a cell [a, b] with a ≥ 0,
a² + 9/4 ≥ 16 and b² + 9/4 ≤ 2(a² + 9/4), the integral of g is at most (b - a) g(a), and so at
most any C above (b - a) ℓ²/(1/4 + a²) for ℓ ≥ log(a² + 9/4). PROVED here, burst-20261122 S8. -/
theorem cell (a b ℓ C : ℝ) (ha : 0 ≤ a) (hu : 16 ≤ a ^ 2 + 9 / 4) (hab : a ≤ b)
    (hb : b ^ 2 + 9 / 4 ≤ 2 * (a ^ 2 + 9 / 4)) (hl : Real.log (a ^ 2 + 9 / 4) ≤ ℓ)
    (hC : (b - a) * ℓ ^ 2 / (1 / 4 + a ^ 2) ≤ C) :
    ∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ C := by
  set K := Real.log (a ^ 2 + 9 / 4) ^ 2 / (1 / 4 + a ^ 2) with hK
  have hmono : ∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ ∫ _ in a..b, K := by
    refine intervalIntegral.integral_mono_on hab (g_cont.intervalIntegrable _ _)
      intervalIntegrable_const (fun τ hτ => ?_)
    have h1 : a ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ ha hτ.1 2
    have h2 : τ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha.trans hτ.1) hτ.2 2
    have := f_anti (a ^ 2 + 9 / 4) (τ ^ 2 + 9 / 4) hu (by linarith) (by linarith)
    rw [hK]
    convert this using 2 <;> ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hL0 : 0 ≤ Real.log (a ^ 2 + 9 / 4) := Real.log_nonneg (by linarith)
  have hsq : Real.log (a ^ 2 + 9 / 4) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hL0 hl 2
  have hden : 0 < 1 / 4 + a ^ 2 := by positivity
  have : (b - a) * K ≤ (b - a) * ℓ ^ 2 / (1 / 4 + a ^ 2) := by
    rw [hK, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hden.le) (by linarith)
  linarith

/-- A rational upper bound for log y, y = 2^k r with r ≥ 1: k log 2 plus the Mercator series
of log r in x = 1 - 1/r to n terms plus its remainder x^(n+1)/(1 - x), from Mathlib's
`Real.abs_log_sub_add_sum_range_le` and log 2 < 0.6931471808. Used for the values of
log(τ² + 9/4) in the cells. PROVED here, burst-20261122 S8. -/
theorem log_le_series (y r : ℝ) (k n : ℕ) (hy : y = 2 ^ k * r) (h1 : 1 ≤ r) (ℓ : ℝ)
    (hS : (k : ℝ) * 0.6931471808 + ∑ i ∈ Finset.range n, (1 - 1 / r) ^ (i + 1) / ((i : ℝ) + 1)
      + (1 - 1 / r) ^ (n + 1) / (1 / r) ≤ ℓ) :
    Real.log y ≤ ℓ := by
  have hr0 : 0 < r := by linarith
  set x := 1 - 1 / r with hx
  have hx0 : 0 ≤ x := by rw [hx, sub_nonneg, div_le_one hr0]; exact h1
  have hx1 : x < 1 := by rw [hx]; have : 0 < 1 / r := by positivity
                         linarith
  have habs := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at habs
  have h1x : 1 - x = 1 / r := by rw [hx]; ring
  rw [h1x, Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub] at habs
  have hlr : Real.log r ≤ ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1) + x ^ (n + 1) / (1 / r) := by
    have := (abs_le.mp habs).1
    linarith
  have hlog2 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k)
  rw [hy, Real.log_mul (by positivity) hr0.ne', Real.log_pow]
  linarith

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
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here, burst-20261122 S8, by left sums over cells with `cell`; the integrand decreases there. -/
theorem piece_11 :
    ∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.675 := by
  have I := fun c d : ℝ => g_cont.intervalIntegrable (μ := MeasureTheory.volume) c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (I 3.8 3.9) (I 3.9 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 3.9 4) (I 4 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4 4.1) (I 4.1 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.1 4.2) (I 4.2 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.2 4.3) (I 4.3 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.3 4.4) (I 4.4 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.4 4.5) (I 4.5 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.5 4.6) (I 4.6 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.6 4.7) (I 4.7 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.7 4.8) (I 4.8 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.8 4.9) (I 4.9 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 4.9 5) (I 5 5.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5 5.1) (I 5.1 5.2)]
  have c0 := cell 3.8 3.9 2.81481 0.053936 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1669/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c1 := cell 3.9 4 2.859913 0.052905 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (873/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c2 := cell 4 4.1 2.904166 0.051903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (73/64) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c3 := cell 4.1 4.2 2.947592 0.050928 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (953/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c4 := cell 4.2 4.3 2.990218 0.04998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1989/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c5 := cell 4.3 4.4 3.032065 0.049058 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1037/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c6 := cell 4.4 4.5 3.073157 0.048161 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2161/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c7 := cell 4.5 4.6 3.113516 0.047288 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (45/32) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c8 := cell 4.6 4.7 3.153164 0.046439 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2341/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c9 := cell 4.7 4.8 3.192122 0.045612 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1217/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c10 := cell 4.8 4.9 3.23041 0.044807 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2529/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c11 := cell 4.9 5 3.268049 0.044024 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1313/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c12 := cell 5 5.1 3.305057 0.043261 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (109/64) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c13 := cell 5.1 5.2 3.341454 0.042519 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1413/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  linarith [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]

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
