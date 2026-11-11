import LeanLab.HelfgottMajor.Moment389
import LeanLab.HelfgottMajor.WeightedMoment389

/-!
Actual Gaussian norms from the scalar power moments of P0014 display 4.42, page 43.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Norm389
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs
open scoped Topology

/-- The derivative of the positive half line Gaussian on its open support, display 4.42. -/
theorem etaHeart_deriv (t : ℝ) (ht : 0 < t) :
    deriv etaHeart t = -t * exp (-t ^ 2 / 2) := by
  have hh : HasDerivAt (fun u : ℝ => exp (-u ^ 2 / 2)) (-t * exp (-t ^ 2 / 2)) t := by
    convert (((hasDerivAt_id t).pow 2).neg.div_const 2).exp using 1 <;> simp <;> ring
  apply HasDerivAt.deriv
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  change 0 < u at hu
  simp [etaHeart, hu]

/-- The Gaussian divided by sqrt t has L1 norm at most 2.15581 on the positive half line.
Source display 4.42, page 43.
-/
theorem etaHeart_half_norm :
    (∫ t in Ioi (0 : ℝ), |etaHeart t| / sqrt t) ≤ 2.15581 := by
  have heq : (∫ t in Ioi (0 : ℝ), |etaHeart t| / sqrt t) =
      ∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only
    rw [etaHeart, ite_eq_left ht, abs_of_pos (exp_pos _), sqrt_eq_rpow, div_eq_mul_inv,
      ← rpow_neg ht.le]
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    ring
  rw [heq]
  exact HalfMoment389.gaussian_half_moment_bound

/-- The derivative divided by sqrt t has L1 norm at most 1.03045 on the positive half line.
Source display 4.42, page 43.
-/
theorem etaHeart_derivative_half_norm :
    (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| / sqrt t) ≤ 1.03045 := by
  have heq : (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| / sqrt t) =
      ∫ t in Ioi (0 : ℝ), t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only
    rw [etaHeart_deriv t ht, abs_mul, abs_neg, abs_of_pos ht,
      abs_of_pos (exp_pos _), sqrt_eq_rpow, div_eq_mul_inv, ← rpow_neg ht.le]
    have hp : t * t ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← rpow_one t]
      rw [← rpow_add ht]
      norm_num
    calc
      _ = (t * t ^ (-(1 / 2 : ℝ))) * exp (-t ^ 2 / 2) := by ring
      _ = _ := by rw [hp]
  rw [heq]
  exact WeightedMoment389.gaussian_half_power_bound

/-- The derivative times sqrt t has L1 norm at most 1.07791 on the positive half line.
Source display 4.42, page 43.
-/
theorem etaHeart_derivative_sqrt_norm :
    (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| * sqrt t) ≤ 1.07791 := by
  have heq : (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| * sqrt t) =
      ∫ t in Ioi (0 : ℝ), t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only
    rw [etaHeart_deriv t ht, abs_mul, abs_neg, abs_of_pos ht,
      abs_of_pos (exp_pos _), sqrt_eq_rpow]
    have hp : t * t ^ (1 / 2 : ℝ) = t ^ (3 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← rpow_one t]
      rw [← rpow_add ht]
      norm_num
    calc
      _ = (t * t ^ (1 / 2 : ℝ)) * exp (-t ^ 2 / 2) := by ring
      _ = _ := by rw [hp]
  rw [heq]
  exact Moment389.three_halves_moment_bound

/-- The Gaussian times sqrt t has L1 norm at most 1.03045, display 4.42 on page 43. -/
theorem etaHeart_sqrt_norm :
    (∫ t in Ioi (0 : ℝ), |etaHeart t| * sqrt t) ≤ 1.03045 := by
  have heq : (∫ t in Ioi (0 : ℝ), |etaHeart t| * sqrt t) =
      ∫ t in Ioi (0 : ℝ), t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only
    rw [etaHeart, ite_eq_left ht, abs_of_pos (exp_pos _), sqrt_eq_rpow]
    ring
  rw [heq]
  exact WeightedMoment389.gaussian_half_power_bound

/-- The actual Gaussian c0 norm budget of display 4.3 and Proposition 4.6, pages 31 and 44.
All four integrals are bounded here without a cited scalar norm input.
-/
theorem gaussian_c0_bound (δ : ℝ) :
    Lemma41Terms.c0
      (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| / sqrt t)
      (∫ t in Ioi (0 : ℝ), |deriv etaHeart t| * sqrt t)
      (∫ t in Ioi (0 : ℝ), |etaHeart t| / sqrt t)
      (∫ t in Ioi (0 : ℝ), |etaHeart t| * sqrt t) |δ| ≤
      1.4056 + 13.3466 * |δ| := by
  have ha := etaHeart_derivative_half_norm
  have hb := etaHeart_derivative_sqrt_norm
  have hc := etaHeart_half_norm
  have hd := etaHeart_sqrt_norm
  calc
    _ ≤ Lemma41Terms.c0 1.03045 1.07791 2.15581 1.03045 |δ| := by
      unfold Lemma41Terms.c0
      gcongr
    _ ≤ _ := Lemma41Terms.c0_gauss (abs_nonneg δ)

end LeanLab.HelfgottMajor.Norm389
