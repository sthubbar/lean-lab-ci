/-
Jia 1996 pages 261 and 262, explicit formulas and the base grid endpoints.
Source https://doi.org/10.4064/aa-77-3-207-287.
These endpoint certificates support the two remaining printed base grids.
They do not certify the intervening grid values.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Buchstab578
import LeanLab.Languasco2004.LogApprox565

namespace LeanLab.Languasco2004.Endpoints578
open Real intervalIntegral Buchstab578 LogApprox565 Finset
noncomputable section
set_option maxHeartbeats 0

/-- Page 262 first grid: the actual endpoint at three satisfies both printed bounds. -/
theorem grid_three_start : 0.56081 ≤ buchstab 3 ∧ buchstab 3 ≤ 0.56439 := by
  rw [buchstab_two_three 3 (by norm_num) (by norm_num)]
  norm_num only
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Page 261 second explicit formula: the actual solution on three through four. -/
theorem buchstab_three_four (u : ℝ) (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    buchstab u = (1 + log (u - 1) + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) / u := by
  have hlow : (∫ t in (1 : ℝ)..2, buchstab t) = log 2 := by
    calc
      _ = ∫ t in (1 : ℝ)..2, 1 / t := by
        apply integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
        exact buchstab_initial t ht.1 ht.2
      _ = log 2 := by rw [integral_one_div_of_pos zero_lt_one (by norm_num : (0 : ℝ) < 2)]; simp
  have hlog : IntervalIntegrable (fun t : ℝ => log (t - 1) / t)
      MeasureTheory.volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro t ht
      linarith [ht.1]
    · fun_prop
    · intro t ht
      linarith [ht.1]
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) MeasureTheory.volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  have hhigh : (∫ t in (2 : ℝ)..(u - 1), buchstab t) =
      log ((u - 1) / 2) + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t := by
    calc
      _ = ∫ t in (2 : ℝ)..(u - 1), (1 / t + log (t - 1) / t) := by
        apply integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)] at ht
        rw [buchstab_two_three t ht.1 (by linarith [ht.2])]
        ring
      _ = _ := by rw [integral_add hinv hlog, integral_one_div_of_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < u - 1)]
  have hadd := integral_add_adjacent_intervals
    (buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume) (1 : ℝ) 2)
    (buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume) 2 (u - 1))
  have h := buchstab_recurrence u (by linarith)
  rw [← hadd, hlow, hhigh, Real.log_div (by linarith : u - 1 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  apply (eq_div_iff (by linarith : u ≠ 0)).mpr
  linarith

/-- Page 261 explicit formula at four: certify the fixed logarithmic integral by the existing enclosure. -/
theorem log_integral_at_four :
    (0.1471 : ℝ) ≤ ∫ t in (2 : ℝ)..3, log (t - 1) / t ∧
      (∫ t in (2 : ℝ)..3, log (t - 1) / t) ≤ 0.1474 := by
  have h := integral_log_approx (2 : ℝ) 3 (-1) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hp : (0.14711 : ℝ) ≤ ∫ t in (2 : ℝ)..3, logPoly (-1 + 1 * t) * recipPoly 3 t ∧
      (∫ t in (2 : ℝ)..3, logPoly (-1 + 1 * t) * recipPoly 3 t) ≤ 0.14739 := by
    unfold logPoly recipPoly
    simp only [sum_range_succ, sum_range_zero]
    ring_nf
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
       integral_pow, integral_const, integral_id, smul_eq_mul]
    norm_num
  have heq : (fun t : ℝ => log (-1 + 1 * t) / t) = fun t => log (t - 1) / t := by
    funext t
    congr 2
    ring
  rw [heq] at h
  obtain ⟨hl, hU⟩ := abs_le.mp h
  constructor <;> linarith [hp.1, hp.2]

/-- Page 262 second grid: the actual value at four satisfies the printed endpoint bounds.
This also supplies the last endpoint of the first grid. -/
theorem grid_four_start : 0.5613 ≤ buchstab 4 ∧ buchstab 4 ≤ 0.5616 := by
  rw [buchstab_three_four 4 (by norm_num) (by norm_num)]
  norm_num only
  have h3 : log (3 : ℝ) = log 2 + log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  rw [h3]
  have hi := log_integral_at_four
  have hlog := log_three_halves_bounds
  constructor <;> linarith [hi.1, hi.2, hlog.1, hlog.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

#print axioms grid_three_start
#print axioms buchstab_three_four
#print axioms log_integral_at_four
#print axioms grid_four_start
end
end LeanLab.Languasco2004.Endpoints578
