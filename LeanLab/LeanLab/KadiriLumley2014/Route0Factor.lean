/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Evaluates from below the factor F_m of page 9, the normalized m-th derivative
factor of equation 2.21 used before Theorem 2.7, at m = 5, for the weight
(4 t (1 - t))^m of Section 3.1 and Table 2 row 1, x0 = 4*10^18, delta = 35800/10^12.
Method: the fourth derivative of the weight is an explicit polynomial, and on a
partition of the unit interval the integral of the absolute fifth derivative is
at least the sum of the absolute increments of the fourth derivative.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.WeightHigherFactor

namespace LeanLab.KadiriLumley2014.Route0
open Real Set MeasureTheory intervalIntegral
open LeanLab.KadiriLumley2014.Task64

/-- Derivative of an explicit real polynomial of degree at most ten. -/
private lemma poly_hasDerivAt (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 t : ℝ) :
    HasDerivAt (fun x : ℝ => c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + c5 * x ^ 5 +
        c6 * x ^ 6 + c7 * x ^ 7 + c8 * x ^ 8 + c9 * x ^ 9 + c10 * x ^ 10)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3 + 5 * c5 * t ^ 4 + 6 * c6 * t ^ 5 +
        7 * c7 * t ^ 6 + 8 * c8 * t ^ 7 + 9 * c9 * t ^ 8 + 10 * c10 * t ^ 9) t := by
  have h := ((((((((((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
    ((hasDerivAt_pow 2 t).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)).add
    ((hasDerivAt_pow 4 t).const_mul c4)).add ((hasDerivAt_pow 5 t).const_mul c5)).add
    ((hasDerivAt_pow 6 t).const_mul c6)).add ((hasDerivAt_pow 7 t).const_mul c7)).add
    ((hasDerivAt_pow 8 t).const_mul c8)).add ((hasDerivAt_pow 9 t).const_mul c9)).add
    ((hasDerivAt_pow 10 t).const_mul c10)
  convert h using 1
  · funext x
    simp
  · simp
    ring

/-- The weight of Section 3.1 at m = 5 in expanded form. -/
private lemma w0 : iteratedDeriv 0 (weight 5) = fun t : ℝ =>
    0 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 1024 * t ^ 5 + (-5120) * t ^ 6 +
      10240 * t ^ 7 + (-10240) * t ^ 8 + 5120 * t ^ 9 + (-1024) * t ^ 10 := by
  funext t
  simp only [iteratedDeriv_zero, weight]
  ring

private lemma w1 : iteratedDeriv 1 (weight 5) = fun t : ℝ =>
    0 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3 + 5120 * t ^ 4 + (-30720) * t ^ 5 + 71680 * t ^ 6 +
      (-81920) * t ^ 7 + 46080 * t ^ 8 + (-10240) * t ^ 9 + 0 * t ^ 10 := by
  rw [iteratedDeriv_succ, w0]
  funext t
  refine HasDerivAt.deriv ?_
  convert poly_hasDerivAt _ _ _ _ _ _ _ _ _ _ _ t using 1
  ring

private lemma w2 : iteratedDeriv 2 (weight 5) = fun t : ℝ =>
    0 + 0 * t + 0 * t ^ 2 + 20480 * t ^ 3 + (-153600) * t ^ 4 + 430080 * t ^ 5 +
      (-573440) * t ^ 6 + 368640 * t ^ 7 + (-92160) * t ^ 8 + 0 * t ^ 9 + 0 * t ^ 10 := by
  rw [iteratedDeriv_succ, w1]
  funext t
  refine HasDerivAt.deriv ?_
  convert poly_hasDerivAt _ _ _ _ _ _ _ _ _ _ _ t using 1
  ring

private lemma w3 : iteratedDeriv 3 (weight 5) = fun t : ℝ =>
    0 + 0 * t + 61440 * t ^ 2 + (-614400) * t ^ 3 + 2150400 * t ^ 4 + (-3440640) * t ^ 5 +
      2580480 * t ^ 6 + (-737280) * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 + 0 * t ^ 10 := by
  rw [iteratedDeriv_succ, w2]
  funext t
  refine HasDerivAt.deriv ?_
  convert poly_hasDerivAt _ _ _ _ _ _ _ _ _ _ _ t using 1
  ring

private lemma w4 : iteratedDeriv 4 (weight 5) = fun t : ℝ =>
    0 + 122880 * t + (-1843200) * t ^ 2 + 8601600 * t ^ 3 + (-17203200) * t ^ 4 +
      15482880 * t ^ 5 + (-5160960) * t ^ 6 + 0 * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 +
      0 * t ^ 10 := by
  rw [iteratedDeriv_succ, w3]
  funext t
  refine HasDerivAt.deriv ?_
  convert poly_hasDerivAt _ _ _ _ _ _ _ _ _ _ _ t using 1
  ring

/-- The fifth derivative is the derivative of the fourth, at every point. -/
private lemma w4_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 4 (weight 5)) (iteratedDeriv 5 (weight 5) t) t := by
  rw [show iteratedDeriv 5 (weight 5) = deriv (iteratedDeriv 4 (weight 5)) from
    iteratedDeriv_succ]
  have hd : DifferentiableAt ℝ (iteratedDeriv 4 (weight 5)) t := by
    rw [w4]
    exact (poly_hasDerivAt _ _ _ _ _ _ _ _ _ _ _ t).differentiableAt
  exact hd.hasDerivAt

private lemma w5_continuous : Continuous (iteratedDeriv 5 (weight 5)) :=
  (weight_contDiff 5).continuous_iteratedDeriv 5 (by simp)

/-- On each piece the integral of the absolute fifth derivative dominates the
absolute increment of the fourth derivative. -/
private lemma piece {a b : ℝ} (hab : a ≤ b) :
    |iteratedDeriv 4 (weight 5) b - iteratedDeriv 4 (weight 5) a| ≤
      ∫ t in a..b, |iteratedDeriv 5 (weight 5) t| := by
  rw [← integral_eq_sub_of_hasDerivAt (fun x _ => w4_hasDerivAt x)
    (w5_continuous.intervalIntegrable a b)]
  exact abs_integral_le_integral_abs hab

/-- The L1 norm of the fifth derivative of the weight (4 t (1 - t))^5, the
numerator of F_5 of page 9 at delta = 0. -/
private lemma abs_w5_integral_ge :
    (31855 : ℝ) ≤ ∫ t in (0 : ℝ)..1, |iteratedDeriv 5 (weight 5) t| := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => |iteratedDeriv 5 (weight 5) t|)
      volume a b := fun a b => w5_continuous.abs.intervalIntegrable a b
  have h1 := piece (a := 0) (b := 47 / 1000) (by norm_num)
  have h2 := piece (a := 47 / 1000) (b := 231 / 1000) (by norm_num)
  have h3 := piece (a := 231 / 1000) (b := 1 / 2) (by norm_num)
  have h4 := piece (a := 1 / 2) (b := 769 / 1000) (by norm_num)
  have h5 := piece (a := 769 / 1000) (b := 953 / 1000) (by norm_num)
  have h6 := piece (a := 953 / 1000) (b := 1) (by norm_num)
  have e1 := le_abs_self (iteratedDeriv 4 (weight 5) (47 / 1000) - iteratedDeriv 4 (weight 5) 0)
  have e2 := neg_le_abs
    (iteratedDeriv 4 (weight 5) (231 / 1000) - iteratedDeriv 4 (weight 5) (47 / 1000))
  have e3 := le_abs_self
    (iteratedDeriv 4 (weight 5) (1 / 2) - iteratedDeriv 4 (weight 5) (231 / 1000))
  have e4 := neg_le_abs
    (iteratedDeriv 4 (weight 5) (769 / 1000) - iteratedDeriv 4 (weight 5) (1 / 2))
  have e5 := le_abs_self
    (iteratedDeriv 4 (weight 5) (953 / 1000) - iteratedDeriv 4 (weight 5) (769 / 1000))
  have e6 := neg_le_abs
    (iteratedDeriv 4 (weight 5) 1 - iteratedDeriv 4 (weight 5) (953 / 1000))
  have s1 := integral_add_adjacent_intervals (hi 0 (47 / 1000)) (hi (47 / 1000) (231 / 1000))
  have s2 := integral_add_adjacent_intervals (hi 0 (231 / 1000)) (hi (231 / 1000) (1 / 2))
  have s3 := integral_add_adjacent_intervals (hi 0 (1 / 2)) (hi (1 / 2) (769 / 1000))
  have s4 := integral_add_adjacent_intervals (hi 0 (769 / 1000)) (hi (769 / 1000) (953 / 1000))
  have s5 := integral_add_adjacent_intervals (hi 0 (953 / 1000)) (hi (953 / 1000) 1)
  have v0 : iteratedDeriv 4 (weight 5) 0 = 0 := by rw [w4]; norm_num
  have v1 : iteratedDeriv 4 (weight 5) (47 / 1000) = 30716849105757273 / 12207031250000 := by
    rw [w4]; norm_num
  have v2 : iteratedDeriv 4 (weight 5) (231 / 1000) =
      -43062411081808503 / 12207031250000 := by
    rw [w4]; norm_num
  have v3 : iteratedDeriv 4 (weight 5) (1 / 2) = 3840 := by rw [w4]; norm_num
  have v4 : iteratedDeriv 4 (weight 5) (769 / 1000) =
      -43062411081808503 / 12207031250000 := by
    rw [w4]; norm_num
  have v5 : iteratedDeriv 4 (weight 5) (953 / 1000) = 30716849105757273 / 12207031250000 := by
    rw [w4]; norm_num
  have v6 : iteratedDeriv 4 (weight 5) 1 = 0 := by rw [w4]; norm_num
  rw [v0, v1] at e1 h1
  rw [v1, v2] at e2 h2
  rw [v2, v3] at e3 h3
  rw [v3, v4] at e4 h4
  rw [v4, v5] at e5 h5
  rw [v5, v6] at e6 h6
  linarith

/-- Lower bound for the factor F_5 of page 9, the normalized fifth derivative
factor of equation 2.21 for the weight (4 t (1 - t))^5 of Section 3.1, uniform
in delta at least zero. The value at delta = 0 is about 86235.41. -/
theorem higherFactor_five_ge {δ : ℝ} (hδ : 0 ≤ δ) : (86200 : ℝ) ≤ higherFactor 5 δ := by
  have hmass : (∫ t in (0 : ℝ)..1, weight 5 t) = 256 / 693 := by
    rw [weight_mass]
    norm_num [Nat.factorial]
  have hmono : (∫ t in (0 : ℝ)..1, |iteratedDeriv 5 (weight 5) t|) ≤
      ∫ t in (0 : ℝ)..1, (1 + δ * t) ^ (5 + 1) * |iteratedDeriv 5 (weight 5) t| := by
    refine integral_mono_on (by norm_num) (w5_continuous.abs.intervalIntegrable 0 1)
      (Continuous.intervalIntegrable (by have := w5_continuous; fun_prop) 0 1) ?_
    intro t ht
    have h1 : (1 : ℝ) ≤ (1 + δ * t) ^ (5 + 1) :=
      one_le_pow₀ (by nlinarith [ht.1])
    exact le_mul_of_one_le_left (abs_nonneg _) h1
  unfold higherFactor
  rw [hmass, le_div_iff₀ (by norm_num)]
  have := abs_w5_integral_ge
  linarith

end LeanLab.KadiriLumley2014.Route0

#print axioms LeanLab.KadiriLumley2014.Route0.higherFactor_five_ge
