/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 175, absolute convergence and cosine orthogonality before display 4.12.
-/
import LeanLab.PlattTrudgian2014.Mixed421

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- P0026 page 175, integer cosine orthogonality on the unit interval. -/
theorem cosine_integer_integral421 (k : ℤ) :
    (∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * k * x)) = if k = 0 then 1 else 0 := by
  have he (x : ℝ) : Real.cos (2 * Real.pi * k * x) = (phase ((k : ℝ) * x)).re := by
    unfold phase
    rw [Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  simp_rw [he]
  exact phase_integer_integral421 k

/-- P0026 page 175, the integral of two cosine modes retains the matching frequency. -/
theorem cosine_modes_integral421 (k n : ℕ) :
    (∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * k * x) *
      Real.cos (2 * Real.pi * n * x)) = if k = n then (if n = 0 then 1 else 1 / 2) else 0 := by
  have he (x : ℝ) :
      2 * (Real.cos (2 * Real.pi * k * x) * Real.cos (2 * Real.pi * n * x)) =
        Real.cos (2 * Real.pi * (((k : ℤ) - n : ℤ) : ℝ) * x) +
          Real.cos (2 * Real.pi * (((k : ℤ) + n : ℤ) : ℝ) * x) := by
    have hsub : 2 * Real.pi * (((k : ℤ) - n : ℤ) : ℝ) * x =
        2 * Real.pi * k * x - 2 * Real.pi * n * x := by push_cast; ring
    have hadd : 2 * Real.pi * (((k : ℤ) + n : ℤ) : ℝ) * x =
        2 * Real.pi * k * x + 2 * Real.pi * n * x := by push_cast; ring
    rw [hsub, hadd]
    simpa only [mul_assoc] using Real.two_mul_cos_mul_cos
      (2 * Real.pi * k * x) (2 * Real.pi * n * x)
  have hi := congrArg (fun f : ℝ → ℝ => ∫ x : ℝ in 0..1, f x) (funext he)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun x : ℝ =>
        Real.cos (2 * Real.pi * (((k : ℤ) - n : ℤ) : ℝ) * x))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ =>
        Real.cos (2 * Real.pi * (((k : ℤ) + n : ℤ) : ℝ) * x))).intervalIntegrable _ _),
    cosine_integer_integral421, cosine_integer_integral421] at hi
  by_cases hkn : k = n
  · subst k
    by_cases hn : n = 0
    · simp [hn]
    · have hp : (n : ℤ) + n ≠ 0 := by omega
      simp [hn, hp] at hi ⊢
      linarith
  · have hm : (k : ℤ) - n ≠ 0 := by omega
    have hp : (k : ℤ) + n ≠ 0 := by omega
    simp [hkn, hm, hp] at hi ⊢
    linarith

/-- P0026 page 175, one cosine coefficient of an absolutely convergent series. -/
theorem cosine_series_coefficient421 (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (n : ℕ) :
    (∫ x : ℝ in 0..1, (∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) *
      Real.cos (2 * Real.pi * n * x)) = if n = 0 then a 0 else a n / 2 := by
  have hb (k : ℕ) (x : ℝ) : ‖a k * Real.cos (2 * Real.pi * k * x)‖ ≤ |a k| := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hb' (k : ℕ) (x : ℝ) : ‖(a k * Real.cos (2 * Real.pi * k * x)) *
      Real.cos (2 * Real.pi * n * x)‖ ≤ |a k| := by
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul (hb k x) (Real.abs_cos_le_one _) (abs_nonneg _) (abs_nonneg _)).trans_eq (mul_one _)
  have hs (x : ℝ) : Summable (fun k : ℕ => a k * Real.cos (2 * Real.pi * k * x)) :=
    ha.of_norm_bounded (fun k => hb k x)
  have hm : HasSum (fun k : ℕ => ∫ x : ℝ in 0..1,
      (a k * Real.cos (2 * Real.pi * k * x)) * Real.cos (2 * Real.pi * n * x))
      (∫ x : ℝ in 0..1, (∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) *
        Real.cos (2 * Real.pi * n * x)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k (_ : ℝ) => |a k|)
    · intro k
      exact (by fun_prop : Continuous (fun x : ℝ =>
        (a k * Real.cos (2 * Real.pi * k * x)) * Real.cos (2 * Real.pi * n * x))).aestronglyMeasurable
    · intro k
      exact Filter.Eventually.of_forall fun x hx => hb' k x
    · exact Filter.Eventually.of_forall fun x hx => ha
    · exact continuous_const.intervalIntegrable 0 1
    · exact Filter.Eventually.of_forall fun x hx => (hs x).hasSum.mul_right _
  have hscalar (k : ℕ) : (∫ x : ℝ in 0..1,
      (a k * Real.cos (2 * Real.pi * k * x)) * Real.cos (2 * Real.pi * n * x)) =
      a k * (if k = n then (if n = 0 then 1 else 1 / 2) else 0) := by
    have he (x : ℝ) : (a k * Real.cos (2 * Real.pi * k * x)) * Real.cos (2 * Real.pi * n * x) =
        a k * (Real.cos (2 * Real.pi * k * x) * Real.cos (2 * Real.pi * n * x)) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, cosine_modes_integral421]
  rw [← hm.tsum_eq]
  simp_rw [hscalar]
  by_cases hn : n = 0
  · simp [hn, mul_ite]
  · simp [hn, mul_ite, div_eq_mul_inv]

/-- P0026 page 175, absolute convergence justifies the dilated cosine product identity. -/
theorem cosine_series_product_proved421 (a b : ℕ → ℝ)
    (ha : Summable (fun k => |a k|)) (hb : Summable (fun k => |b k|))
    (q : ℕ) (hq : 0 < q) :
    (∫ x : ℝ in 0..1,
      (∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)) *
        (∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))) =
      a 0 * b 0 + (1 / 2 : ℝ) * ∑' k : ℕ, a ((k + 1) * q) * b (k + 1) := by
  let f : ℝ → ℝ := fun x => ∑' k : ℕ, a k * Real.cos (2 * Real.pi * k * x)
  let A : ℝ := ∑' k : ℕ, |a k|
  have hA : 0 ≤ A := tsum_nonneg fun k => abs_nonneg _
  have ha_bound (k : ℕ) (x : ℝ) : ‖a k * Real.cos (2 * Real.pi * k * x)‖ ≤ |a k| := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hf : Continuous f := continuous_tsum (fun k => by fun_prop) ha ha_bound
  have hf_bound (x : ℝ) : ‖f x‖ ≤ A := by
    have hs : Summable (fun k : ℕ => ‖a k * Real.cos (2 * Real.pi * k * x)‖) :=
      ha.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ha_bound k x)
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun k => ha_bound k x) ha)
  have hb_bound (k : ℕ) (x : ℝ) : ‖b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x))‖ ≤ |b k| := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hprod_bound (k : ℕ) (x : ℝ) :
      ‖f x * (b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))‖ ≤ A * |b k| := by
    rw [norm_mul]
    exact mul_le_mul (hf_bound x) (hb_bound k x) (norm_nonneg _) hA
  have hm : HasSum (fun k : ℕ => ∫ x : ℝ in 0..1,
      f x * (b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x))))
      (∫ x : ℝ in 0..1, f x * (∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k (_ : ℝ) => A * |b k|)
    · intro k
      exact (hf.mul (by fun_prop : Continuous (fun x : ℝ =>
        b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x))))).aestronglyMeasurable
    · intro k
      exact Filter.Eventually.of_forall fun x hx => hprod_bound k x
    · exact Filter.Eventually.of_forall fun x hx => hb.mul_left A
    · exact continuous_const.intervalIntegrable 0 1
    · exact Filter.Eventually.of_forall fun x hx =>
        (hb.of_norm_bounded (fun k => hb_bound k x)).hasSum.mul_left (f x)
  have hi (k : ℕ) : (∫ x : ℝ in 0..1,
      f x * (b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))) =
        b k * (if k * q = 0 then a 0 else a (k * q) / 2) := by
    have he (x : ℝ) : f x * (b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x))) =
        b k * (f x * Real.cos (2 * Real.pi * ((k * q : ℕ) : ℝ) * x)) := by
      push_cast
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact cosine_series_coefficient421 a ha (k * q)
  have hs : Summable (fun k : ℕ => b k * (if k * q = 0 then a 0 else a (k * q) / 2)) :=
    hm.summable.congr hi
  change (∫ x : ℝ in 0..1, f x * (∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * ((q : ℝ) * x)))) = _
  rw [← hm.tsum_eq]
  simp_rw [hi]
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.zero_mul, ite_true]
  have hqk (k : ℕ) : (k + 1) * q ≠ 0 := Nat.mul_ne_zero (by omega) hq.ne'
  simp_rw [if_neg (hqk _)]
  have he (k : ℕ) : b (k + 1) * (a ((k + 1) * q) / 2) =
      (1 / 2 : ℝ) * (a ((k + 1) * q) * b (k + 1)) := by ring
  simp_rw [he]
  rw [tsum_mul_left]
  ring

set_option format.width 240
#print axioms cosine_integer_integral421
#print axioms cosine_modes_integral421
#print axioms cosine_series_coefficient421
#print axioms cosine_series_product_proved421

end LeanLab.PlattTrudgian2014
