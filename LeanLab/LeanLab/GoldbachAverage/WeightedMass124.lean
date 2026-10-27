import LeanLab.GoldbachAverage.WeightedCauchy124
import LeanLab.GoldbachAverage.Sliding124

/-!
The integrability needed for P0051 page 11 weighted tail estimates.
The only growth input is Mathlib's proved elementary Chebyshev bound.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedMass124
open MeasureTheory Filter Set
open FloorVariance82

/-- An elementary global linear bound for the coefficient counting error R.
Source context: the weighted R integrals on P0051 pages 10 and 11. -/
theorem R_linear_bound {t : ℝ} (ht : 0 ≤ t) : |psiFloorError t| ≤ 8 * (t + 1) := by
  have hp := Chebyshev.psi_le_const_mul_self ht
  have hl : Real.log (4 : ℝ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hl ht
  have hp0 := Chebyshev.psi_nonneg t
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  rw [psiFloorError, abs_le]
  constructor <;> nlinarith

/-- The weighted R square has finite mass on the positive half line.
Source: P0051 page 11, the integrals after eq. 55. -/
theorem weighted_R_square_integrable (N : ℕ) (hN : 1 ≤ N) :
    IntegrableOn (fun t : ℝ => psiFloorError t ^ 2 * Real.exp (-2 * t / N)) (Ioi 0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℝ := 2 / N
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-a * t)) (Ioi 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := 2) (b := a) (by norm_num) (by norm_num) ha
  have he : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 0) := by
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := 0) (b := a) (by norm_num) (by norm_num) ha
  have hm : IntegrableOn (fun t : ℝ =>
      128 * (t ^ 2 * Real.exp (-a * t) + Real.exp (-a * t))) (Ioi 0) :=
    (hp.add he).const_mul 128
  have hi : IntegrableOn (fun t : ℝ => psiFloorError t ^ 2 * Real.exp (-a * t))
      (Ioi 0) := by
    refine hm.mono' (((measurable_psiFloorError.pow_const 2).mul (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := pow_le_pow_left₀ (abs_nonneg (psiFloorError t)) (R_linear_bound ht.le) 2
    rw [sq_abs] at hb
    have hb2 : psiFloorError t ^ 2 ≤ 128 * (t ^ 2 + 1) := by
      nlinarith [sq_nonneg (t - 1)]
    calc psiFloorError t ^ 2 * Real.exp (-a * t)
        ≤ (128 * (t ^ 2 + 1)) * Real.exp (-a * t) :=
          mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le
      _ = _ := by ring
  convert hi using 1
  funext t
  congr 1
  congr 1
  dsimp [a]
  ring

end LeanLab.GoldbachAverage.WeightedMass124
