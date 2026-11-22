import Mathlib
import LeanLab.HelfgottMajor.IntegralCells680

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
  have c0 := IntegralCells680.cell_bound 1.2 1.2125 1.31377 0.0127663
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.31377) 12))
    (by norm_num)
  have c1 := IntegralCells680.cell_bound 1.2125 1.225 1.32193 0.0126987
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.32193) 12))
    (by norm_num)
  have c2 := IntegralCells680.cell_bound 1.225 1.2375 1.3301 0.0126324
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.3301) 12))
    (by norm_num)
  have c3 := IntegralCells680.cell_bound 1.2375 1.25 1.33829 0.0125675
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.33829) 12))
    (by norm_num)
  have c4 := IntegralCells680.cell_bound 1.25 1.2625 1.34649 0.0125037
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.34649) 12))
    (by norm_num)
  have c5 := IntegralCells680.cell_bound 1.2625 1.275 1.35471 0.0124413
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.35471) 12))
    (by norm_num)
  have c6 := IntegralCells680.cell_bound 1.275 1.2875 1.36294 0.01238
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.36294) 12))
    (by norm_num)
  have c7 := IntegralCells680.cell_bound 1.2875 1.3 1.37119 0.0123199
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.37119) 12))
    (by norm_num)
  have c8 := IntegralCells680.cell_bound 1.3 1.3125 1.37944 0.0122607
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.37944) 12))
    (by norm_num)
  have c9 := IntegralCells680.cell_bound 1.3125 1.325 1.3877 0.0122026
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.3877) 12))
    (by norm_num)
  have c10 := IntegralCells680.cell_bound 1.325 1.3375 1.39598 0.0121456
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.39598) 12))
    (by norm_num)
  have c11 := IntegralCells680.cell_bound 1.3375 1.35 1.40426 0.0120895
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.40426) 12))
    (by norm_num)
  have c12 := IntegralCells680.cell_bound 1.35 1.3625 1.41255 0.0120344
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.41255) 12))
    (by norm_num)
  have c13 := IntegralCells680.cell_bound 1.3625 1.375 1.42085 0.0119803
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.42085) 12))
    (by norm_num)
  have c14 := IntegralCells680.cell_bound 1.375 1.3875 1.42916 0.011927
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.42916) 12))
    (by norm_num)
  have c15 := IntegralCells680.cell_bound 1.3875 1.4 1.43747 0.0118746
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.43747) 12))
    (by norm_num)
  have c16 := IntegralCells680.cell_bound 1.4 1.4125 1.44578 0.0118229
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.44578) 12))
    (by norm_num)
  have c17 := IntegralCells680.cell_bound 1.4125 1.425 1.4541 0.0117721
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.4541) 12))
    (by norm_num)
  have c18 := IntegralCells680.cell_bound 1.425 1.4375 1.46243 0.0117222
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.46243) 12))
    (by norm_num)
  have c19 := IntegralCells680.cell_bound 1.4375 1.45 1.47076 0.011673
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.47076) 12))
    (by norm_num)
  have c20 := IntegralCells680.cell_bound 1.45 1.4625 1.47909 0.0116244
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.47909) 12))
    (by norm_num)
  have c21 := IntegralCells680.cell_bound 1.4625 1.475 1.48742 0.0115766
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.48742) 12))
    (by norm_num)
  have c22 := IntegralCells680.cell_bound 1.475 1.4875 1.49575 0.0115294
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.49575) 12))
    (by norm_num)
  have c23 := IntegralCells680.cell_bound 1.4875 1.5 1.50408 0.0114829
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.50408) 12))
    (by norm_num)
  have c24 := IntegralCells680.cell_bound 1.5 1.5125 1.51242 0.0114371
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.51242) 12))
    (by norm_num)
  have c25 := IntegralCells680.cell_bound 1.5125 1.525 1.52075 0.0113919
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.52075) 12))
    (by norm_num)
  have c26 := IntegralCells680.cell_bound 1.525 1.5375 1.52908 0.0113472
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.52908) 12))
    (by norm_num)
  have c27 := IntegralCells680.cell_bound 1.5375 1.55 1.53741 0.0113032
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.53741) 12))
    (by norm_num)
  have c28 := IntegralCells680.cell_bound 1.55 1.5625 1.54574 0.0112598
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.54574) 12))
    (by norm_num)
  have c29 := IntegralCells680.cell_bound 1.5625 1.575 1.55406 0.0112168
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.55406) 12))
    (by norm_num)
  have c30 := IntegralCells680.cell_bound 1.575 1.5875 1.56238 0.0111744
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.56238) 12))
    (by norm_num)
  have c31 := IntegralCells680.cell_bound 1.5875 1.6 1.5707 0.0111325
    (by norm_num) (by norm_num)
    (by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.5707) 12))
    (by norm_num)
  have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
      (1 / 4 + τ ^ 2)) :=
    Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
      (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.2125)
    (hc.intervalIntegrable 1.2125 1.225)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.225)
    (hc.intervalIntegrable 1.225 1.2375)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.2375)
    (hc.intervalIntegrable 1.2375 1.25)
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.25)
    (hc.intervalIntegrable 1.25 1.2625)
  have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.2625)
    (hc.intervalIntegrable 1.2625 1.275)
  have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.275)
    (hc.intervalIntegrable 1.275 1.2875)
  have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.2875)
    (hc.intervalIntegrable 1.2875 1.3)
  have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.3)
    (hc.intervalIntegrable 1.3 1.3125)
  have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.3125)
    (hc.intervalIntegrable 1.3125 1.325)
  have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.325)
    (hc.intervalIntegrable 1.325 1.3375)
  have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.3375)
    (hc.intervalIntegrable 1.3375 1.35)
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.35)
    (hc.intervalIntegrable 1.35 1.3625)
  have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.3625)
    (hc.intervalIntegrable 1.3625 1.375)
  have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.375)
    (hc.intervalIntegrable 1.375 1.3875)
  have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.3875)
    (hc.intervalIntegrable 1.3875 1.4)
  have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.4)
    (hc.intervalIntegrable 1.4 1.4125)
  have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.4125)
    (hc.intervalIntegrable 1.4125 1.425)
  have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.425)
    (hc.intervalIntegrable 1.425 1.4375)
  have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.4375)
    (hc.intervalIntegrable 1.4375 1.45)
  have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.45)
    (hc.intervalIntegrable 1.45 1.4625)
  have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.4625)
    (hc.intervalIntegrable 1.4625 1.475)
  have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.475)
    (hc.intervalIntegrable 1.475 1.4875)
  have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.4875)
    (hc.intervalIntegrable 1.4875 1.5)
  have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.5)
    (hc.intervalIntegrable 1.5 1.5125)
  have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.5125)
    (hc.intervalIntegrable 1.5125 1.525)
  have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.525)
    (hc.intervalIntegrable 1.525 1.5375)
  have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.5375)
    (hc.intervalIntegrable 1.5375 1.55)
  have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.55)
    (hc.intervalIntegrable 1.55 1.5625)
  have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.5625)
    (hc.intervalIntegrable 1.5625 1.575)
  have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.575)
    (hc.intervalIntegrable 1.575 1.5875)
  have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 1.2 1.5875)
    (hc.intervalIntegrable 1.5875 1.6)
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [1.6, 2.1]: ∫ g ≤ 0.417;
the true value is 0.4109. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_08 :
    ∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.417 := by
  set_option maxHeartbeats 2000000 in
    have c0 := IntegralCells680.cell_bound 1.6 1.6078125 1.5759 0.0069047
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.5759) 12))
      (by norm_num)
    have c1 := IntegralCells680.cell_bound 1.6078125 1.615625 1.58109 0.0068888
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.58109) 12))
      (by norm_num)
    have c2 := IntegralCells680.cell_bound 1.615625 1.6234375 1.58629 0.0068731
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.58629) 12))
      (by norm_num)
    have c3 := IntegralCells680.cell_bound 1.6234375 1.63125 1.59148 0.0068575
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.59148) 12))
      (by norm_num)
    have c4 := IntegralCells680.cell_bound 1.63125 1.6390625 1.59667 0.006842
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.59667) 12))
      (by norm_num)
    have c5 := IntegralCells680.cell_bound 1.6390625 1.646875 1.60185 0.0068266
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.60185) 12))
      (by norm_num)
    have c6 := IntegralCells680.cell_bound 1.646875 1.6546875 1.60704 0.0068113
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.60704) 12))
      (by norm_num)
    have c7 := IntegralCells680.cell_bound 1.6546875 1.6625 1.61222 0.0067961
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.61222) 12))
      (by norm_num)
    have c8 := IntegralCells680.cell_bound 1.6625 1.6703125 1.6174 0.0067811
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.6174) 12))
      (by norm_num)
    have c9 := IntegralCells680.cell_bound 1.6703125 1.678125 1.62258 0.0067661
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.62258) 12))
      (by norm_num)
    have c10 := IntegralCells680.cell_bound 1.678125 1.6859375 1.62775 0.0067512
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.62775) 12))
      (by norm_num)
    have c11 := IntegralCells680.cell_bound 1.6859375 1.69375 1.63292 0.0067364
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.63292) 12))
      (by norm_num)
    have c12 := IntegralCells680.cell_bound 1.69375 1.7015625 1.63809 0.0067218
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.63809) 12))
      (by norm_num)
    have c13 := IntegralCells680.cell_bound 1.7015625 1.709375 1.64326 0.0067072
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.64326) 12))
      (by norm_num)
    have c14 := IntegralCells680.cell_bound 1.709375 1.7171875 1.64842 0.0066927
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.64842) 12))
      (by norm_num)
    have c15 := IntegralCells680.cell_bound 1.7171875 1.725 1.65358 0.0066783
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.65358) 12))
      (by norm_num)
    have c16 := IntegralCells680.cell_bound 1.725 1.7328125 1.65874 0.006664
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.65874) 12))
      (by norm_num)
    have c17 := IntegralCells680.cell_bound 1.7328125 1.740625 1.66389 0.0066498
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.66389) 12))
      (by norm_num)
    have c18 := IntegralCells680.cell_bound 1.740625 1.7484375 1.66904 0.0066356
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.66904) 12))
      (by norm_num)
    have c19 := IntegralCells680.cell_bound 1.7484375 1.75625 1.67418 0.0066215
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.67418) 12))
      (by norm_num)
    have c20 := IntegralCells680.cell_bound 1.75625 1.7640625 1.67933 0.0066076
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.67933) 12))
      (by norm_num)
    have c21 := IntegralCells680.cell_bound 1.7640625 1.771875 1.68447 0.0065938
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.68447) 12))
      (by norm_num)
    have c22 := IntegralCells680.cell_bound 1.771875 1.7796875 1.6896 0.0065799
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.6896) 12))
      (by norm_num)
    have c23 := IntegralCells680.cell_bound 1.7796875 1.7875 1.69473 0.0065662
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.69473) 12))
      (by norm_num)
    have c24 := IntegralCells680.cell_bound 1.7875 1.7953125 1.69986 0.0065526
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.69986) 12))
      (by norm_num)
    have c25 := IntegralCells680.cell_bound 1.7953125 1.803125 1.70498 0.006539
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.70498) 12))
      (by norm_num)
    have c26 := IntegralCells680.cell_bound 1.803125 1.8109375 1.7101 0.0065255
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.7101) 12))
      (by norm_num)
    have c27 := IntegralCells680.cell_bound 1.8109375 1.81875 1.71522 0.0065121
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.71522) 12))
      (by norm_num)
    have c28 := IntegralCells680.cell_bound 1.81875 1.8265625 1.72033 0.0064987
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.72033) 12))
      (by norm_num)
    have c29 := IntegralCells680.cell_bound 1.8265625 1.834375 1.72543 0.0064854
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.72543) 12))
      (by norm_num)
    have c30 := IntegralCells680.cell_bound 1.834375 1.8421875 1.73054 0.0064723
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.73054) 12))
      (by norm_num)
    have c31 := IntegralCells680.cell_bound 1.8421875 1.85 1.73564 0.0064592
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.73564) 12))
      (by norm_num)
    have c32 := IntegralCells680.cell_bound 1.85 1.8578125 1.74073 0.0064461
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.74073) 12))
      (by norm_num)
    have c33 := IntegralCells680.cell_bound 1.8578125 1.865625 1.74582 0.0064331
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.74582) 12))
      (by norm_num)
    have c34 := IntegralCells680.cell_bound 1.865625 1.8734375 1.7509 0.0064201
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.7509) 12))
      (by norm_num)
    have c35 := IntegralCells680.cell_bound 1.8734375 1.88125 1.75598 0.0064072
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.75598) 12))
      (by norm_num)
    have c36 := IntegralCells680.cell_bound 1.88125 1.8890625 1.76106 0.0063945
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.76106) 12))
      (by norm_num)
    have c37 := IntegralCells680.cell_bound 1.8890625 1.896875 1.76613 0.0063817
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.76613) 12))
      (by norm_num)
    have c38 := IntegralCells680.cell_bound 1.896875 1.9046875 1.77119 0.006369
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.77119) 12))
      (by norm_num)
    have c39 := IntegralCells680.cell_bound 1.9046875 1.9125 1.77625 0.0063564
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.77625) 12))
      (by norm_num)
    have c40 := IntegralCells680.cell_bound 1.9125 1.9203125 1.78131 0.0063439
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.78131) 12))
      (by norm_num)
    have c41 := IntegralCells680.cell_bound 1.9203125 1.928125 1.78636 0.0063314
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.78636) 12))
      (by norm_num)
    have c42 := IntegralCells680.cell_bound 1.928125 1.9359375 1.79141 0.006319
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.79141) 12))
      (by norm_num)
    have c43 := IntegralCells680.cell_bound 1.9359375 1.94375 1.79645 0.0063066
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.79645) 12))
      (by norm_num)
    have c44 := IntegralCells680.cell_bound 1.94375 1.9515625 1.80148 0.0062943
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.80148) 12))
      (by norm_num)
    have c45 := IntegralCells680.cell_bound 1.9515625 1.959375 1.80651 0.006282
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.80651) 12))
      (by norm_num)
    have c46 := IntegralCells680.cell_bound 1.959375 1.9671875 1.81154 0.0062698
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.81154) 12))
      (by norm_num)
    have c47 := IntegralCells680.cell_bound 1.9671875 1.975 1.81656 0.0062577
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.81656) 12))
      (by norm_num)
    have c48 := IntegralCells680.cell_bound 1.975 1.9828125 1.82157 0.0062456
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.82157) 12))
      (by norm_num)
    have c49 := IntegralCells680.cell_bound 1.9828125 1.990625 1.82658 0.0062335
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.82658) 12))
      (by norm_num)
    have c50 := IntegralCells680.cell_bound 1.990625 1.9984375 1.83159 0.0062216
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.83159) 12))
      (by norm_num)
    have c51 := IntegralCells680.cell_bound 1.9984375 2.00625 1.83659 0.0062097
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.83659) 12))
      (by norm_num)
    have c52 := IntegralCells680.cell_bound 2.00625 2.0140625 1.84158 0.0061978
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.84158) 12))
      (by norm_num)
    have c53 := IntegralCells680.cell_bound 2.0140625 2.021875 1.84657 0.0061859
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.84657) 12))
      (by norm_num)
    have c54 := IntegralCells680.cell_bound 2.021875 2.0296875 1.85155 0.0061741
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.85155) 12))
      (by norm_num)
    have c55 := IntegralCells680.cell_bound 2.0296875 2.0375 1.85652 0.0061624
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.85652) 12))
      (by norm_num)
    have c56 := IntegralCells680.cell_bound 2.0375 2.0453125 1.86149 0.0061507
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.86149) 12))
      (by norm_num)
    have c57 := IntegralCells680.cell_bound 2.0453125 2.053125 1.86646 0.0061391
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.86646) 12))
      (by norm_num)
    have c58 := IntegralCells680.cell_bound 2.053125 2.0609375 1.87142 0.0061275
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.87142) 12))
      (by norm_num)
    have c59 := IntegralCells680.cell_bound 2.0609375 2.06875 1.87637 0.0061159
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.87637) 12))
      (by norm_num)
    have c60 := IntegralCells680.cell_bound 2.06875 2.0765625 1.88132 0.0061045
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.88132) 12))
      (by norm_num)
    have c61 := IntegralCells680.cell_bound 2.0765625 2.084375 1.88626 0.006093
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.88626) 12))
      (by norm_num)
    have c62 := IntegralCells680.cell_bound 2.084375 2.0921875 1.8912 0.0060816
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.8912) 12))
      (by norm_num)
    have c63 := IntegralCells680.cell_bound 2.0921875 2.1 1.89613 0.0060703
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.89613) 12))
      (by norm_num)
    have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
        (1 / 4 + τ ^ 2)) :=
      Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
        (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6078125)
      (hc.intervalIntegrable 1.6078125 1.615625)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.615625)
      (hc.intervalIntegrable 1.615625 1.6234375)
    have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6234375)
      (hc.intervalIntegrable 1.6234375 1.63125)
    have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.63125)
      (hc.intervalIntegrable 1.63125 1.6390625)
    have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6390625)
      (hc.intervalIntegrable 1.6390625 1.646875)
    have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.646875)
      (hc.intervalIntegrable 1.646875 1.6546875)
    have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6546875)
      (hc.intervalIntegrable 1.6546875 1.6625)
    have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6625)
      (hc.intervalIntegrable 1.6625 1.6703125)
    have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6703125)
      (hc.intervalIntegrable 1.6703125 1.678125)
    have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.678125)
      (hc.intervalIntegrable 1.678125 1.6859375)
    have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.6859375)
      (hc.intervalIntegrable 1.6859375 1.69375)
    have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.69375)
      (hc.intervalIntegrable 1.69375 1.7015625)
    have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7015625)
      (hc.intervalIntegrable 1.7015625 1.709375)
    have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.709375)
      (hc.intervalIntegrable 1.709375 1.7171875)
    have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7171875)
      (hc.intervalIntegrable 1.7171875 1.725)
    have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.725)
      (hc.intervalIntegrable 1.725 1.7328125)
    have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7328125)
      (hc.intervalIntegrable 1.7328125 1.740625)
    have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.740625)
      (hc.intervalIntegrable 1.740625 1.7484375)
    have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7484375)
      (hc.intervalIntegrable 1.7484375 1.75625)
    have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.75625)
      (hc.intervalIntegrable 1.75625 1.7640625)
    have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7640625)
      (hc.intervalIntegrable 1.7640625 1.771875)
    have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.771875)
      (hc.intervalIntegrable 1.771875 1.7796875)
    have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7796875)
      (hc.intervalIntegrable 1.7796875 1.7875)
    have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7875)
      (hc.intervalIntegrable 1.7875 1.7953125)
    have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.7953125)
      (hc.intervalIntegrable 1.7953125 1.803125)
    have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.803125)
      (hc.intervalIntegrable 1.803125 1.8109375)
    have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8109375)
      (hc.intervalIntegrable 1.8109375 1.81875)
    have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.81875)
      (hc.intervalIntegrable 1.81875 1.8265625)
    have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8265625)
      (hc.intervalIntegrable 1.8265625 1.834375)
    have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.834375)
      (hc.intervalIntegrable 1.834375 1.8421875)
    have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8421875)
      (hc.intervalIntegrable 1.8421875 1.85)
    have h32 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.85)
      (hc.intervalIntegrable 1.85 1.8578125)
    have h33 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8578125)
      (hc.intervalIntegrable 1.8578125 1.865625)
    have h34 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.865625)
      (hc.intervalIntegrable 1.865625 1.8734375)
    have h35 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8734375)
      (hc.intervalIntegrable 1.8734375 1.88125)
    have h36 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.88125)
      (hc.intervalIntegrable 1.88125 1.8890625)
    have h37 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.8890625)
      (hc.intervalIntegrable 1.8890625 1.896875)
    have h38 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.896875)
      (hc.intervalIntegrable 1.896875 1.9046875)
    have h39 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9046875)
      (hc.intervalIntegrable 1.9046875 1.9125)
    have h40 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9125)
      (hc.intervalIntegrable 1.9125 1.9203125)
    have h41 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9203125)
      (hc.intervalIntegrable 1.9203125 1.928125)
    have h42 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.928125)
      (hc.intervalIntegrable 1.928125 1.9359375)
    have h43 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9359375)
      (hc.intervalIntegrable 1.9359375 1.94375)
    have h44 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.94375)
      (hc.intervalIntegrable 1.94375 1.9515625)
    have h45 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9515625)
      (hc.intervalIntegrable 1.9515625 1.959375)
    have h46 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.959375)
      (hc.intervalIntegrable 1.959375 1.9671875)
    have h47 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9671875)
      (hc.intervalIntegrable 1.9671875 1.975)
    have h48 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.975)
      (hc.intervalIntegrable 1.975 1.9828125)
    have h49 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9828125)
      (hc.intervalIntegrable 1.9828125 1.990625)
    have h50 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.990625)
      (hc.intervalIntegrable 1.990625 1.9984375)
    have h51 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 1.9984375)
      (hc.intervalIntegrable 1.9984375 2.00625)
    have h52 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.00625)
      (hc.intervalIntegrable 2.00625 2.0140625)
    have h53 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0140625)
      (hc.intervalIntegrable 2.0140625 2.021875)
    have h54 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.021875)
      (hc.intervalIntegrable 2.021875 2.0296875)
    have h55 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0296875)
      (hc.intervalIntegrable 2.0296875 2.0375)
    have h56 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0375)
      (hc.intervalIntegrable 2.0375 2.0453125)
    have h57 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0453125)
      (hc.intervalIntegrable 2.0453125 2.053125)
    have h58 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.053125)
      (hc.intervalIntegrable 2.053125 2.0609375)
    have h59 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0609375)
      (hc.intervalIntegrable 2.0609375 2.06875)
    have h60 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.06875)
      (hc.intervalIntegrable 2.06875 2.0765625)
    have h61 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0765625)
      (hc.intervalIntegrable 2.0765625 2.084375)
    have h62 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.084375)
      (hc.intervalIntegrable 2.084375 2.0921875)
    have h63 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 1.6 2.0921875)
      (hc.intervalIntegrable 2.0921875 2.1)
    rw [← h63, ← h62, ← h61, ← h60, ← h59, ← h58, ← h57, ← h56, ← h55, ← h54, ← h53, ← h52, ← h51, ← h50, ← h49, ← h48, ← h47, ← h46, ← h45, ← h44, ← h43, ← h42, ← h41, ← h40, ← h39, ← h38, ← h37, ← h36, ← h35, ← h34, ← h33, ← h32, ← h31, ← h30, ← h29, ← h28, ← h27, ← h26, ← h25, ← h24, ← h23, ← h22, ← h21, ← h20, ← h19, ← h18, ← h17, ← h16, ← h15, ← h14, ← h13, ← h12, ← h11, ← h10, ← h9, ← h8, ← h7, ← h6, ← h5, ← h4, ← h3, ← h2, ← h1]
    linarith only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.1, 2.8]: ∫ g ≤ 0.506;
the true value is 0.4995. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_09 :
    ∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.506 := by
  set_option maxHeartbeats 2000000 in
    have c0 := IntegralCells680.cell_bound 2.1 2.1109375 1.90302 0.0085
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.90302) 12))
      (by norm_num)
    have c1 := IntegralCells680.cell_bound 2.1109375 2.121875 1.9099 0.0084778
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.9099) 12))
      (by norm_num)
    have c2 := IntegralCells680.cell_bound 2.121875 2.1328125 1.91677 0.0084557
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.91677) 12))
      (by norm_num)
    have c3 := IntegralCells680.cell_bound 2.1328125 2.14375 1.92362 0.0084337
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.92362) 12))
      (by norm_num)
    have c4 := IntegralCells680.cell_bound 2.14375 2.1546875 1.93047 0.0084119
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.93047) 12))
      (by norm_num)
    have c5 := IntegralCells680.cell_bound 2.1546875 2.165625 1.9373 0.0083901
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.9373) 12))
      (by norm_num)
    have c6 := IntegralCells680.cell_bound 2.165625 2.1765625 1.94412 0.0083685
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.94412) 12))
      (by norm_num)
    have c7 := IntegralCells680.cell_bound 2.1765625 2.1875 1.95093 0.0083469
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.95093) 12))
      (by norm_num)
    have c8 := IntegralCells680.cell_bound 2.1875 2.1984375 1.95772 0.0083255
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.95772) 12))
      (by norm_num)
    have c9 := IntegralCells680.cell_bound 2.1984375 2.209375 1.9645 0.0083041
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.9645) 12))
      (by norm_num)
    have c10 := IntegralCells680.cell_bound 2.209375 2.2203125 1.97128 0.008283
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.97128) 12))
      (by norm_num)
    have c11 := IntegralCells680.cell_bound 2.2203125 2.23125 1.97803 0.0082618
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.97803) 12))
      (by norm_num)
    have c12 := IntegralCells680.cell_bound 2.23125 2.2421875 1.98478 0.0082408
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.98478) 12))
      (by norm_num)
    have c13 := IntegralCells680.cell_bound 2.2421875 2.253125 1.99151 0.0082199
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.99151) 12))
      (by norm_num)
    have c14 := IntegralCells680.cell_bound 2.253125 2.2640625 1.99823 0.0081991
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.99823) 12))
      (by norm_num)
    have c15 := IntegralCells680.cell_bound 2.2640625 2.275 2.00494 0.0081784
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.00494) 12))
      (by norm_num)
    have c16 := IntegralCells680.cell_bound 2.275 2.2859375 2.01164 0.0081578
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.01164) 12))
      (by norm_num)
    have c17 := IntegralCells680.cell_bound 2.2859375 2.296875 2.01832 0.0081372
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.01832) 12))
      (by norm_num)
    have c18 := IntegralCells680.cell_bound 2.296875 2.3078125 2.02499 0.0081168
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.02499) 12))
      (by norm_num)
    have c19 := IntegralCells680.cell_bound 2.3078125 2.31875 2.03165 0.0080965
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.03165) 12))
      (by norm_num)
    have c20 := IntegralCells680.cell_bound 2.31875 2.3296875 2.03829 0.0080762
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.03829) 12))
      (by norm_num)
    have c21 := IntegralCells680.cell_bound 2.3296875 2.340625 2.04492 0.008056
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.04492) 12))
      (by norm_num)
    have c22 := IntegralCells680.cell_bound 2.340625 2.3515625 2.05154 0.008036
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.05154) 12))
      (by norm_num)
    have c23 := IntegralCells680.cell_bound 2.3515625 2.3625 2.05815 0.008016
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.05815) 12))
      (by norm_num)
    have c24 := IntegralCells680.cell_bound 2.3625 2.3734375 2.06474 0.0079961
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.06474) 12))
      (by norm_num)
    have c25 := IntegralCells680.cell_bound 2.3734375 2.384375 2.07132 0.0079763
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.07132) 12))
      (by norm_num)
    have c26 := IntegralCells680.cell_bound 2.384375 2.3953125 2.07789 0.0079566
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.07789) 12))
      (by norm_num)
    have c27 := IntegralCells680.cell_bound 2.3953125 2.40625 2.08444 0.0079369
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.08444) 12))
      (by norm_num)
    have c28 := IntegralCells680.cell_bound 2.40625 2.4171875 2.09098 0.0079174
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.09098) 12))
      (by norm_num)
    have c29 := IntegralCells680.cell_bound 2.4171875 2.428125 2.09751 0.0078979
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.09751) 12))
      (by norm_num)
    have c30 := IntegralCells680.cell_bound 2.428125 2.4390625 2.10402 0.0078785
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.10402) 12))
      (by norm_num)
    have c31 := IntegralCells680.cell_bound 2.4390625 2.45 2.11052 0.0078592
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.11052) 12))
      (by norm_num)
    have c32 := IntegralCells680.cell_bound 2.45 2.4609375 2.11701 0.0078399
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.11701) 12))
      (by norm_num)
    have c33 := IntegralCells680.cell_bound 2.4609375 2.471875 2.12349 0.0078208
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.12349) 12))
      (by norm_num)
    have c34 := IntegralCells680.cell_bound 2.471875 2.4828125 2.12995 0.0078017
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.12995) 12))
      (by norm_num)
    have c35 := IntegralCells680.cell_bound 2.4828125 2.49375 2.1364 0.0077827
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.1364) 12))
      (by norm_num)
    have c36 := IntegralCells680.cell_bound 2.49375 2.5046875 2.14283 0.0077638
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.14283) 12))
      (by norm_num)
    have c37 := IntegralCells680.cell_bound 2.5046875 2.515625 2.14925 0.0077449
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.14925) 12))
      (by norm_num)
    have c38 := IntegralCells680.cell_bound 2.515625 2.5265625 2.15566 0.0077262
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.15566) 12))
      (by norm_num)
    have c39 := IntegralCells680.cell_bound 2.5265625 2.5375 2.16206 0.0077075
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.16206) 12))
      (by norm_num)
    have c40 := IntegralCells680.cell_bound 2.5375 2.5484375 2.16844 0.0076888
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.16844) 12))
      (by norm_num)
    have c41 := IntegralCells680.cell_bound 2.5484375 2.559375 2.17481 0.0076703
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.17481) 12))
      (by norm_num)
    have c42 := IntegralCells680.cell_bound 2.559375 2.5703125 2.18116 0.0076518
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.18116) 12))
      (by norm_num)
    have c43 := IntegralCells680.cell_bound 2.5703125 2.58125 2.1875 0.0076333
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.1875) 12))
      (by norm_num)
    have c44 := IntegralCells680.cell_bound 2.58125 2.5921875 2.19383 0.007615
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.19383) 12))
      (by norm_num)
    have c45 := IntegralCells680.cell_bound 2.5921875 2.603125 2.20015 0.0075968
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.20015) 12))
      (by norm_num)
    have c46 := IntegralCells680.cell_bound 2.603125 2.6140625 2.20645 0.0075785
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.20645) 12))
      (by norm_num)
    have c47 := IntegralCells680.cell_bound 2.6140625 2.625 2.21274 0.0075604
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.21274) 12))
      (by norm_num)
    have c48 := IntegralCells680.cell_bound 2.625 2.6359375 2.21901 0.0075423
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.21901) 12))
      (by norm_num)
    have c49 := IntegralCells680.cell_bound 2.6359375 2.646875 2.22528 0.0075243
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.22528) 12))
      (by norm_num)
    have c50 := IntegralCells680.cell_bound 2.646875 2.6578125 2.23152 0.0075063
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.23152) 12))
      (by norm_num)
    have c51 := IntegralCells680.cell_bound 2.6578125 2.66875 2.23776 0.0074885
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.23776) 12))
      (by norm_num)
    have c52 := IntegralCells680.cell_bound 2.66875 2.6796875 2.24398 0.0074707
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.24398) 12))
      (by norm_num)
    have c53 := IntegralCells680.cell_bound 2.6796875 2.690625 2.25019 0.0074529
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.25019) 12))
      (by norm_num)
    have c54 := IntegralCells680.cell_bound 2.690625 2.7015625 2.25639 0.0074353
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.25639) 12))
      (by norm_num)
    have c55 := IntegralCells680.cell_bound 2.7015625 2.7125 2.26257 0.0074177
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.26257) 12))
      (by norm_num)
    have c56 := IntegralCells680.cell_bound 2.7125 2.7234375 2.26874 0.0074001
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.26874) 12))
      (by norm_num)
    have c57 := IntegralCells680.cell_bound 2.7234375 2.734375 2.2749 0.0073827
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.2749) 12))
      (by norm_num)
    have c58 := IntegralCells680.cell_bound 2.734375 2.7453125 2.28104 0.0073652
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.28104) 12))
      (by norm_num)
    have c59 := IntegralCells680.cell_bound 2.7453125 2.75625 2.28717 0.0073479
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.28717) 12))
      (by norm_num)
    have c60 := IntegralCells680.cell_bound 2.75625 2.7671875 2.29328 0.0073305
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.29328) 12))
      (by norm_num)
    have c61 := IntegralCells680.cell_bound 2.7671875 2.778125 2.29939 0.0073134
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.29939) 12))
      (by norm_num)
    have c62 := IntegralCells680.cell_bound 2.778125 2.7890625 2.30548 0.0072962
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.30548) 12))
      (by norm_num)
    have c63 := IntegralCells680.cell_bound 2.7890625 2.8 2.31156 0.0072791
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.31156) 12))
      (by norm_num)
    have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
        (1 / 4 + τ ^ 2)) :=
      Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
        (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1109375)
      (hc.intervalIntegrable 2.1109375 2.121875)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.121875)
      (hc.intervalIntegrable 2.121875 2.1328125)
    have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1328125)
      (hc.intervalIntegrable 2.1328125 2.14375)
    have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.14375)
      (hc.intervalIntegrable 2.14375 2.1546875)
    have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1546875)
      (hc.intervalIntegrable 2.1546875 2.165625)
    have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.165625)
      (hc.intervalIntegrable 2.165625 2.1765625)
    have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1765625)
      (hc.intervalIntegrable 2.1765625 2.1875)
    have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1875)
      (hc.intervalIntegrable 2.1875 2.1984375)
    have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.1984375)
      (hc.intervalIntegrable 2.1984375 2.209375)
    have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.209375)
      (hc.intervalIntegrable 2.209375 2.2203125)
    have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.2203125)
      (hc.intervalIntegrable 2.2203125 2.23125)
    have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.23125)
      (hc.intervalIntegrable 2.23125 2.2421875)
    have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.2421875)
      (hc.intervalIntegrable 2.2421875 2.253125)
    have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.253125)
      (hc.intervalIntegrable 2.253125 2.2640625)
    have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.2640625)
      (hc.intervalIntegrable 2.2640625 2.275)
    have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.275)
      (hc.intervalIntegrable 2.275 2.2859375)
    have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.2859375)
      (hc.intervalIntegrable 2.2859375 2.296875)
    have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.296875)
      (hc.intervalIntegrable 2.296875 2.3078125)
    have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3078125)
      (hc.intervalIntegrable 2.3078125 2.31875)
    have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.31875)
      (hc.intervalIntegrable 2.31875 2.3296875)
    have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3296875)
      (hc.intervalIntegrable 2.3296875 2.340625)
    have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.340625)
      (hc.intervalIntegrable 2.340625 2.3515625)
    have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3515625)
      (hc.intervalIntegrable 2.3515625 2.3625)
    have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3625)
      (hc.intervalIntegrable 2.3625 2.3734375)
    have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3734375)
      (hc.intervalIntegrable 2.3734375 2.384375)
    have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.384375)
      (hc.intervalIntegrable 2.384375 2.3953125)
    have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.3953125)
      (hc.intervalIntegrable 2.3953125 2.40625)
    have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.40625)
      (hc.intervalIntegrable 2.40625 2.4171875)
    have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.4171875)
      (hc.intervalIntegrable 2.4171875 2.428125)
    have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.428125)
      (hc.intervalIntegrable 2.428125 2.4390625)
    have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.4390625)
      (hc.intervalIntegrable 2.4390625 2.45)
    have h32 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.45)
      (hc.intervalIntegrable 2.45 2.4609375)
    have h33 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.4609375)
      (hc.intervalIntegrable 2.4609375 2.471875)
    have h34 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.471875)
      (hc.intervalIntegrable 2.471875 2.4828125)
    have h35 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.4828125)
      (hc.intervalIntegrable 2.4828125 2.49375)
    have h36 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.49375)
      (hc.intervalIntegrable 2.49375 2.5046875)
    have h37 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5046875)
      (hc.intervalIntegrable 2.5046875 2.515625)
    have h38 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.515625)
      (hc.intervalIntegrable 2.515625 2.5265625)
    have h39 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5265625)
      (hc.intervalIntegrable 2.5265625 2.5375)
    have h40 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5375)
      (hc.intervalIntegrable 2.5375 2.5484375)
    have h41 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5484375)
      (hc.intervalIntegrable 2.5484375 2.559375)
    have h42 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.559375)
      (hc.intervalIntegrable 2.559375 2.5703125)
    have h43 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5703125)
      (hc.intervalIntegrable 2.5703125 2.58125)
    have h44 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.58125)
      (hc.intervalIntegrable 2.58125 2.5921875)
    have h45 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.5921875)
      (hc.intervalIntegrable 2.5921875 2.603125)
    have h46 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.603125)
      (hc.intervalIntegrable 2.603125 2.6140625)
    have h47 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.6140625)
      (hc.intervalIntegrable 2.6140625 2.625)
    have h48 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.625)
      (hc.intervalIntegrable 2.625 2.6359375)
    have h49 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.6359375)
      (hc.intervalIntegrable 2.6359375 2.646875)
    have h50 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.646875)
      (hc.intervalIntegrable 2.646875 2.6578125)
    have h51 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.6578125)
      (hc.intervalIntegrable 2.6578125 2.66875)
    have h52 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.66875)
      (hc.intervalIntegrable 2.66875 2.6796875)
    have h53 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.6796875)
      (hc.intervalIntegrable 2.6796875 2.690625)
    have h54 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.690625)
      (hc.intervalIntegrable 2.690625 2.7015625)
    have h55 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7015625)
      (hc.intervalIntegrable 2.7015625 2.7125)
    have h56 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7125)
      (hc.intervalIntegrable 2.7125 2.7234375)
    have h57 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7234375)
      (hc.intervalIntegrable 2.7234375 2.734375)
    have h58 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.734375)
      (hc.intervalIntegrable 2.734375 2.7453125)
    have h59 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7453125)
      (hc.intervalIntegrable 2.7453125 2.75625)
    have h60 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.75625)
      (hc.intervalIntegrable 2.75625 2.7671875)
    have h61 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7671875)
      (hc.intervalIntegrable 2.7671875 2.778125)
    have h62 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.778125)
      (hc.intervalIntegrable 2.778125 2.7890625)
    have h63 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.1 2.7890625)
      (hc.intervalIntegrable 2.7890625 2.8)
    rw [← h63, ← h62, ← h61, ← h60, ← h59, ← h58, ← h57, ← h56, ← h55, ← h54, ← h53, ← h52, ← h51, ← h50, ← h49, ← h48, ← h47, ← h46, ← h45, ← h44, ← h43, ← h42, ← h41, ← h40, ← h39, ← h38, ← h37, ← h36, ← h35, ← h34, ← h33, ← h32, ← h31, ← h30, ← h29, ← h28, ← h27, ← h26, ← h25, ← h24, ← h23, ← h22, ← h21, ← h20, ← h19, ← h18, ← h17, ← h16, ← h15, ← h14, ← h13, ← h12, ← h11, ← h10, ← h9, ← h8, ← h7, ← h6, ← h5, ← h4, ← h3, ← h2, ← h1]
    linarith only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63]


/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.8, 3.8]: ∫ g ≤ 0.604;
the true value is 0.5970. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_10 :
    ∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.604 := by
  set_option maxHeartbeats 2000000 in
    have c0 := IntegralCells680.cell_bound 2.8 2.815625 2.32021 0.0103975
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.32021) 12))
      (by norm_num)
    have c1 := IntegralCells680.cell_bound 2.815625 2.83125 2.32885 0.0103627
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.32885) 12))
      (by norm_num)
    have c2 := IntegralCells680.cell_bound 2.83125 2.846875 2.33745 0.0103279
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.33745) 12))
      (by norm_num)
    have c3 := IntegralCells680.cell_bound 2.846875 2.8625 2.34603 0.0102934
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.34603) 12))
      (by norm_num)
    have c4 := IntegralCells680.cell_bound 2.8625 2.878125 2.35458 0.010259
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.35458) 12))
      (by norm_num)
    have c5 := IntegralCells680.cell_bound 2.878125 2.89375 2.36311 0.0102249
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.36311) 12))
      (by norm_num)
    have c6 := IntegralCells680.cell_bound 2.89375 2.909375 2.37161 0.0101909
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.37161) 12))
      (by norm_num)
    have c7 := IntegralCells680.cell_bound 2.909375 2.925 2.38008 0.010157
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.38008) 12))
      (by norm_num)
    have c8 := IntegralCells680.cell_bound 2.925 2.940625 2.38853 0.0101233
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.38853) 12))
      (by norm_num)
    have c9 := IntegralCells680.cell_bound 2.940625 2.95625 2.39695 0.0100898
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.39695) 12))
      (by norm_num)
    have c10 := IntegralCells680.cell_bound 2.95625 2.971875 2.40534 0.0100564
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.40534) 12))
      (by norm_num)
    have c11 := IntegralCells680.cell_bound 2.971875 2.9875 2.41371 0.0100233
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.41371) 12))
      (by norm_num)
    have c12 := IntegralCells680.cell_bound 2.9875 3.003125 2.42205 0.0099902
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.42205) 12))
      (by norm_num)
    have c13 := IntegralCells680.cell_bound 3.003125 3.01875 2.43036 0.0099573
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.43036) 12))
      (by norm_num)
    have c14 := IntegralCells680.cell_bound 3.01875 3.034375 2.43865 0.0099246
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.43865) 12))
      (by norm_num)
    have c15 := IntegralCells680.cell_bound 3.034375 3.05 2.44692 0.0098921
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.44692) 12))
      (by norm_num)
    have c16 := IntegralCells680.cell_bound 3.05 3.065625 2.45515 0.0098596
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.45515) 12))
      (by norm_num)
    have c17 := IntegralCells680.cell_bound 3.065625 3.08125 2.46337 0.0098275
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.46337) 12))
      (by norm_num)
    have c18 := IntegralCells680.cell_bound 3.08125 3.096875 2.47155 0.0097953
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.47155) 12))
      (by norm_num)
    have c19 := IntegralCells680.cell_bound 3.096875 3.1125 2.47971 0.0097634
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.47971) 12))
      (by norm_num)
    have c20 := IntegralCells680.cell_bound 3.1125 3.128125 2.48785 0.0097317
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.48785) 12))
      (by norm_num)
    have c21 := IntegralCells680.cell_bound 3.128125 3.14375 2.49596 0.0097
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.49596) 12))
      (by norm_num)
    have c22 := IntegralCells680.cell_bound 3.14375 3.159375 2.50404 0.0096685
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.50404) 12))
      (by norm_num)
    have c23 := IntegralCells680.cell_bound 3.159375 3.175 2.5121 0.0096372
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.5121) 12))
      (by norm_num)
    have c24 := IntegralCells680.cell_bound 3.175 3.190625 2.52014 0.0096061
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.52014) 12))
      (by norm_num)
    have c25 := IntegralCells680.cell_bound 3.190625 3.20625 2.52815 0.009575
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.52815) 12))
      (by norm_num)
    have c26 := IntegralCells680.cell_bound 3.20625 3.221875 2.53613 0.0095441
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.53613) 12))
      (by norm_num)
    have c27 := IntegralCells680.cell_bound 3.221875 3.2375 2.54409 0.0095134
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.54409) 12))
      (by norm_num)
    have c28 := IntegralCells680.cell_bound 3.2375 3.253125 2.55203 0.0094828
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.55203) 12))
      (by norm_num)
    have c29 := IntegralCells680.cell_bound 3.253125 3.26875 2.55994 0.0094524
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.55994) 12))
      (by norm_num)
    have c30 := IntegralCells680.cell_bound 3.26875 3.284375 2.56782 0.009422
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.56782) 12))
      (by norm_num)
    have c31 := IntegralCells680.cell_bound 3.284375 3.3 2.57568 0.0093918
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.57568) 12))
      (by norm_num)
    have c32 := IntegralCells680.cell_bound 3.3 3.315625 2.58352 0.0093618
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.58352) 12))
      (by norm_num)
    have c33 := IntegralCells680.cell_bound 3.315625 3.33125 2.59133 0.0093319
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.59133) 12))
      (by norm_num)
    have c34 := IntegralCells680.cell_bound 3.33125 3.346875 2.59912 0.0093022
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.59912) 12))
      (by norm_num)
    have c35 := IntegralCells680.cell_bound 3.346875 3.3625 2.60688 0.0092726
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.60688) 12))
      (by norm_num)
    have c36 := IntegralCells680.cell_bound 3.3625 3.378125 2.61462 0.0092431
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.61462) 12))
      (by norm_num)
    have c37 := IntegralCells680.cell_bound 3.378125 3.39375 2.62234 0.0092138
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.62234) 12))
      (by norm_num)
    have c38 := IntegralCells680.cell_bound 3.39375 3.409375 2.63003 0.0091846
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.63003) 12))
      (by norm_num)
    have c39 := IntegralCells680.cell_bound 3.409375 3.425 2.6377 0.0091555
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.6377) 12))
      (by norm_num)
    have c40 := IntegralCells680.cell_bound 3.425 3.440625 2.64534 0.0091265
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.64534) 12))
      (by norm_num)
    have c41 := IntegralCells680.cell_bound 3.440625 3.45625 2.65296 0.0090977
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.65296) 12))
      (by norm_num)
    have c42 := IntegralCells680.cell_bound 3.45625 3.471875 2.66056 0.0090691
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.66056) 12))
      (by norm_num)
    have c43 := IntegralCells680.cell_bound 3.471875 3.4875 2.66814 0.0090406
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.66814) 12))
      (by norm_num)
    have c44 := IntegralCells680.cell_bound 3.4875 3.503125 2.67569 0.0090122
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.67569) 12))
      (by norm_num)
    have c45 := IntegralCells680.cell_bound 3.503125 3.51875 2.68321 0.0089838
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.68321) 12))
      (by norm_num)
    have c46 := IntegralCells680.cell_bound 3.51875 3.534375 2.69072 0.0089557
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.69072) 12))
      (by norm_num)
    have c47 := IntegralCells680.cell_bound 3.534375 3.55 2.6982 0.0089277
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.6982) 12))
      (by norm_num)
    have c48 := IntegralCells680.cell_bound 3.55 3.565625 2.70566 0.0088998
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.70566) 12))
      (by norm_num)
    have c49 := IntegralCells680.cell_bound 3.565625 3.58125 2.71309 0.008872
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.71309) 12))
      (by norm_num)
    have c50 := IntegralCells680.cell_bound 3.58125 3.596875 2.72051 0.0088444
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.72051) 12))
      (by norm_num)
    have c51 := IntegralCells680.cell_bound 3.596875 3.6125 2.7279 0.0088169
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.7279) 12))
      (by norm_num)
    have c52 := IntegralCells680.cell_bound 3.6125 3.628125 2.73527 0.0087895
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.73527) 12))
      (by norm_num)
    have c53 := IntegralCells680.cell_bound 3.628125 3.64375 2.74261 0.0087622
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.74261) 12))
      (by norm_num)
    have c54 := IntegralCells680.cell_bound 3.64375 3.659375 2.74993 0.0087351
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.74993) 12))
      (by norm_num)
    have c55 := IntegralCells680.cell_bound 3.659375 3.675 2.75723 0.0087081
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.75723) 12))
      (by norm_num)
    have c56 := IntegralCells680.cell_bound 3.675 3.690625 2.76451 0.0086812
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.76451) 12))
      (by norm_num)
    have c57 := IntegralCells680.cell_bound 3.690625 3.70625 2.77177 0.0086544
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.77177) 12))
      (by norm_num)
    have c58 := IntegralCells680.cell_bound 3.70625 3.721875 2.77901 0.0086278
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.77901) 12))
      (by norm_num)
    have c59 := IntegralCells680.cell_bound 3.721875 3.7375 2.78622 0.0086013
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.78622) 12))
      (by norm_num)
    have c60 := IntegralCells680.cell_bound 3.7375 3.753125 2.79341 0.0085748
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.79341) 12))
      (by norm_num)
    have c61 := IntegralCells680.cell_bound 3.753125 3.76875 2.80058 0.0085485
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.80058) 12))
      (by norm_num)
    have c62 := IntegralCells680.cell_bound 3.76875 3.784375 2.80773 0.0085224
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.80773) 12))
      (by norm_num)
    have c63 := IntegralCells680.cell_bound 3.784375 3.8 2.81485 0.0084963
      (by norm_num) (by norm_num)
      (by
        apply (Real.log_le_iff_le_exp (by norm_num)).2
        exact le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.81485) 12))
      (by norm_num)
    have hc : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 /
        (1 / 4 + τ ^ 2)) :=
      Continuous.div (Continuous.pow (Continuous.log (by fun_prop)
        (fun τ => by positivity)) 2) (by fun_prop) (fun τ => by positivity)
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.815625)
      (hc.intervalIntegrable 2.815625 2.83125)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.83125)
      (hc.intervalIntegrable 2.83125 2.846875)
    have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.846875)
      (hc.intervalIntegrable 2.846875 2.8625)
    have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.8625)
      (hc.intervalIntegrable 2.8625 2.878125)
    have h5 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.878125)
      (hc.intervalIntegrable 2.878125 2.89375)
    have h6 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.89375)
      (hc.intervalIntegrable 2.89375 2.909375)
    have h7 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.909375)
      (hc.intervalIntegrable 2.909375 2.925)
    have h8 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.925)
      (hc.intervalIntegrable 2.925 2.940625)
    have h9 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.940625)
      (hc.intervalIntegrable 2.940625 2.95625)
    have h10 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.95625)
      (hc.intervalIntegrable 2.95625 2.971875)
    have h11 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.971875)
      (hc.intervalIntegrable 2.971875 2.9875)
    have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 2.9875)
      (hc.intervalIntegrable 2.9875 3.003125)
    have h13 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.003125)
      (hc.intervalIntegrable 3.003125 3.01875)
    have h14 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.01875)
      (hc.intervalIntegrable 3.01875 3.034375)
    have h15 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.034375)
      (hc.intervalIntegrable 3.034375 3.05)
    have h16 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.05)
      (hc.intervalIntegrable 3.05 3.065625)
    have h17 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.065625)
      (hc.intervalIntegrable 3.065625 3.08125)
    have h18 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.08125)
      (hc.intervalIntegrable 3.08125 3.096875)
    have h19 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.096875)
      (hc.intervalIntegrable 3.096875 3.1125)
    have h20 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.1125)
      (hc.intervalIntegrable 3.1125 3.128125)
    have h21 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.128125)
      (hc.intervalIntegrable 3.128125 3.14375)
    have h22 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.14375)
      (hc.intervalIntegrable 3.14375 3.159375)
    have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.159375)
      (hc.intervalIntegrable 3.159375 3.175)
    have h24 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.175)
      (hc.intervalIntegrable 3.175 3.190625)
    have h25 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.190625)
      (hc.intervalIntegrable 3.190625 3.20625)
    have h26 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.20625)
      (hc.intervalIntegrable 3.20625 3.221875)
    have h27 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.221875)
      (hc.intervalIntegrable 3.221875 3.2375)
    have h28 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.2375)
      (hc.intervalIntegrable 3.2375 3.253125)
    have h29 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.253125)
      (hc.intervalIntegrable 3.253125 3.26875)
    have h30 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.26875)
      (hc.intervalIntegrable 3.26875 3.284375)
    have h31 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.284375)
      (hc.intervalIntegrable 3.284375 3.3)
    have h32 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.3)
      (hc.intervalIntegrable 3.3 3.315625)
    have h33 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.315625)
      (hc.intervalIntegrable 3.315625 3.33125)
    have h34 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.33125)
      (hc.intervalIntegrable 3.33125 3.346875)
    have h35 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.346875)
      (hc.intervalIntegrable 3.346875 3.3625)
    have h36 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.3625)
      (hc.intervalIntegrable 3.3625 3.378125)
    have h37 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.378125)
      (hc.intervalIntegrable 3.378125 3.39375)
    have h38 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.39375)
      (hc.intervalIntegrable 3.39375 3.409375)
    have h39 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.409375)
      (hc.intervalIntegrable 3.409375 3.425)
    have h40 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.425)
      (hc.intervalIntegrable 3.425 3.440625)
    have h41 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.440625)
      (hc.intervalIntegrable 3.440625 3.45625)
    have h42 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.45625)
      (hc.intervalIntegrable 3.45625 3.471875)
    have h43 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.471875)
      (hc.intervalIntegrable 3.471875 3.4875)
    have h44 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.4875)
      (hc.intervalIntegrable 3.4875 3.503125)
    have h45 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.503125)
      (hc.intervalIntegrable 3.503125 3.51875)
    have h46 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.51875)
      (hc.intervalIntegrable 3.51875 3.534375)
    have h47 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.534375)
      (hc.intervalIntegrable 3.534375 3.55)
    have h48 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.55)
      (hc.intervalIntegrable 3.55 3.565625)
    have h49 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.565625)
      (hc.intervalIntegrable 3.565625 3.58125)
    have h50 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.58125)
      (hc.intervalIntegrable 3.58125 3.596875)
    have h51 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.596875)
      (hc.intervalIntegrable 3.596875 3.6125)
    have h52 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.6125)
      (hc.intervalIntegrable 3.6125 3.628125)
    have h53 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.628125)
      (hc.intervalIntegrable 3.628125 3.64375)
    have h54 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.64375)
      (hc.intervalIntegrable 3.64375 3.659375)
    have h55 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.659375)
      (hc.intervalIntegrable 3.659375 3.675)
    have h56 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.675)
      (hc.intervalIntegrable 3.675 3.690625)
    have h57 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.690625)
      (hc.intervalIntegrable 3.690625 3.70625)
    have h58 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.70625)
      (hc.intervalIntegrable 3.70625 3.721875)
    have h59 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.721875)
      (hc.intervalIntegrable 3.721875 3.7375)
    have h60 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.7375)
      (hc.intervalIntegrable 3.7375 3.753125)
    have h61 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.753125)
      (hc.intervalIntegrable 3.753125 3.76875)
    have h62 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.76875)
      (hc.intervalIntegrable 3.76875 3.784375)
    have h63 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable 2.8 3.784375)
      (hc.intervalIntegrable 3.784375 3.8)
    rw [← h63, ← h62, ← h61, ← h60, ← h59, ← h58, ← h57, ← h56, ← h55, ← h54, ← h53, ← h52, ← h51, ← h50, ← h49, ← h48, ← h47, ← h46, ← h45, ← h44, ← h43, ← h42, ← h41, ← h40, ← h39, ← h38, ← h37, ← h36, ← h35, ← h34, ← h33, ← h32, ← h31, ← h30, ← h29, ← h28, ← h27, ← h26, ← h25, ← h24, ← h23, ← h22, ← h21, ← h20, ← h19, ← h18, ← h17, ← h16, ← h15, ← h14, ← h13, ← h12, ← h11, ← h10, ← h9, ← h8, ← h7, ← h6, ← h5, ← h4, ← h3, ← h2, ← h1]
    linarith only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63]


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
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here, burst-20261122 S8, by left sums over cells with `cell`; the integrand decreases there. -/
theorem piece_12 :
    ∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.728 := by
  have I := fun c d : ℝ => g_cont.intervalIntegrable (μ := MeasureTheory.volume) c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (I 5.2 5.3) (I 5.3 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.3 5.4) (I 5.4 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.4 5.5) (I 5.5 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.5 5.6) (I 5.6 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.6 5.7) (I 5.7 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.7 5.8) (I 5.8 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.8 5.9) (I 5.9 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 5.9 6) (I 6 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6 6.1) (I 6.1 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.1 6.2) (I 6.2 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.2 6.3) (I 6.3 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.3 6.4) (I 6.4 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.4 6.5) (I 6.5 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.5 6.6) (I 6.6 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.6 6.7) (I 6.7 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.7 6.8) (I 6.8 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.8 6.9) (I 6.9 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 6.9 7) (I 7 7.2),
    ← intervalIntegral.integral_add_adjacent_intervals (I 7 7.1) (I 7.1 7.2)]
  have c0 := cell 5.2 5.3 3.377259 0.041796 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2929/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c1 := cell 5.3 5.4 3.412491 0.041091 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1517/800) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c2 := cell 5.4 5.5 3.447169 0.040405 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (3141/1600) 4 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c3 := cell 5.5 5.6 3.481241 0.039735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (65/64) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c4 := cell 5.6 5.7 3.514824 0.039083 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (3361/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c5 := cell 5.7 5.8 3.547892 0.038447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1737/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c6 := cell 5.8 5.9 3.580459 0.037828 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (3589/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c7 := cell 5.9 6 3.612539 0.037224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1853/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c8 := cell 6 6.1 3.644144 0.036634 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (153/128) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c9 := cell 6.1 6.2 3.675288 0.03606 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (1973/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c10 := cell 6.2 6.3 3.705983 0.035499 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (4069/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c11 := cell 6.3 6.4 3.736241 0.034952 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2097/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c12 := cell 6.4 6.5 3.766072 0.034418 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (4321/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c13 := cell 6.5 6.6 3.79549 0.033896 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (89/64) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c14 := cell 6.6 6.7 3.824503 0.033387 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (4581/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c15 := cell 6.7 6.8 3.853122 0.032891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2357/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c16 := cell 6.8 6.9 3.881358 0.032405 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (4849/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c17 := cell 6.9 7 3.90922 0.031931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2493/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c18 := cell 7 7.1 3.936717 0.031468 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (205/128) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c19 := cell 7.1 7.2 3.963858 0.031015 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (2633/1600) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  linarith [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19]

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [7.2, 10]: ∫ g ≤ 0.732;
the true value is 0.7147. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here, burst-20261122 S8, by left sums over cells with `cell`; the integrand decreases there. -/
theorem piece_13 :
    ∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.732 := by
  have I := fun c d : ℝ => g_cont.intervalIntegrable (μ := MeasureTheory.volume) c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (I 7.2 7.4) (I 7.4 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 7.4 7.6) (I 7.6 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 7.6 7.8) (I 7.8 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 7.8 8) (I 8 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 8 8.2) (I 8.2 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 8.2 8.4) (I 8.4 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 8.4 8.6) (I 8.6 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 8.6 8.8) (I 8.8 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 8.8 9) (I 9 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 9 9.2) (I 9.2 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 9.2 9.4) (I 9.4 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 9.4 9.6) (I 9.6 10),
    ← intervalIntegral.integral_add_adjacent_intervals (I 9.6 9.8) (I 9.8 10)]
  have c0 := cell 7.2 7.4 3.990652 0.061146 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (5409/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c1 := cell 7.4 7.6 4.043234 0.059436 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (5701/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c2 := cell 7.6 7.8 4.094531 0.057802 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (6001/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c3 := cell 7.8 8 4.144608 0.056238 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (6309/3200) 5 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c4 := cell 8 8.2 4.193436 0.05474 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (265/256) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c5 := cell 8.2 8.4 4.241183 0.053305 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (6949/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c6 := cell 8.4 8.6 4.287854 0.05193 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (7281/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c7 := cell 8.6 8.8 4.333493 0.050611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (7621/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c8 := cell 8.8 9 4.378145 0.049346 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (7969/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c9 := cell 9 9.2 4.421849 0.04813 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (333/256) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c10 := cell 9.2 9.4 4.464643 0.046963 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (8689/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c11 := cell 9.4 9.6 4.506565 0.04584 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (9061/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c12 := cell 9.6 9.8 4.547648 0.04476 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (9441/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  have c13 := cell 9.8 10 4.587923 0.043721 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_series _ (9829/6400) 6 14 (by norm_num) (by norm_num) _
      (by norm_num [Finset.sum_range_succ])) (by norm_num)
  linarith [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]

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
