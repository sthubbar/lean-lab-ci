/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 Section 7 page 184, pressure criterion, specialized to the lab h equals two bound.
These are limitations of that bound, not refutations of the published lambda values.
-/
import LeanLab.PlattTrudgian2014.LambdaTwo

namespace LeanLab.PlattTrudgian2014

open Finset

/-- A tangent bound for the logarithm of the exact two block factor. -/
theorem log_twoBlockFactor_tangent125 {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (2 * r ^ 2 - 2 / r) / (r ^ 2 + 1 + 2 / r) * (t - Real.log r) +
      Real.log (twoBlockFactor (Real.log r)) ≤ Real.log (twoBlockFactor t) := by
  let S := r ^ 2 + 1 + 2 / r
  have hS : 0 < S := by dsimp [S]; positivity
  let w : Fin 3 → ℝ := ![r ^ 2 / S, 1 / S, (2 / r) / S]
  let p : Fin 3 → ℝ := ![2 * (t - Real.log r), 0, -(t - Real.log r)]
  have hw : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i <;> dsimp [w] <;> positivity
  have hsum : ∑ i : Fin 3, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
    dsimp [S]
    field_simp
    ring
  have hj := convexOn_exp.map_sum_le (t := (univ : Finset (Fin 3)))
    (w := w) (p := p) hw hsum (by simp)
  have harg : (∑ i : Fin 3, w i * p i) =
      (2 * r ^ 2 - 2 / r) / S * (t - Real.log r) := by
    simp [w, p, Fin.sum_univ_succ]
    ring
  simp only [smul_eq_mul, harg] at hj
  have hbase : 0 < twoBlockFactor (Real.log r) := by unfold twoBlockFactor; positivity
  have htpos : 0 < twoBlockFactor t := by unfold twoBlockFactor; positivity
  have hm := mul_le_mul_of_nonneg_right hj hbase.le
  have he2 : Real.exp (2 * (t - Real.log r)) = Real.exp (2 * t) / r ^ 2 := by
    rw [mul_sub, Real.exp_sub,
      show 2 * Real.log r = Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_log hr]
    ring
  have hem : Real.exp (Real.log r - t) = r * Real.exp (-t) := by
    rw [Real.exp_sub, Real.exp_log hr, Real.exp_neg]
    ring
  have heq : (∑ i : Fin 3, w i * Real.exp (p i)) * twoBlockFactor (Real.log r) =
      twoBlockFactor t := by
    norm_num [w, p, Fin.sum_univ_succ]
    rw [he2, hem, twoBlockFactor_log hr]
    dsimp [S]
    unfold twoBlockFactor
    field_simp [hr.ne', hS.ne'] <;> ring
  rw [heq] at hm
  apply Real.exp_le_exp.mp
  rw [Real.exp_add, Real.exp_log hbase, Real.exp_log htpos]
  exact hm

set_option maxHeartbeats 1000000 in
/-- No nonnegative parameter makes the h equals two bound reach the unconditional target. -/
theorem h2_uncond_all_parameters_insufficient125 {t : ℝ} (ht : 0 ≤ t) :
    t * 0.8594 - Real.log (twoBlockFactor t) / 2 < (109 / 154 : ℝ) * Real.log 2 := by
  have hh := log_twoBlockFactor_tangent125 (r := 7 / 2) (by norm_num) t
  rw [twoBlockFactor_log (by norm_num : (0 : ℝ) < 7 / 2)] at hh
  norm_num at hh
  have hr : Real.log (7 / 2 : ℝ) < 1.254 := by
    have h := Real.sum_range_sub_log_div_le (x := (5 / 9 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ] at h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    linarith
  have hF : (1.239 : ℝ) < Real.log (387 / 112) := by
    have h := Real.sum_range_sub_log_div_le (x := (275 / 499 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ] at h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    linarith
  have hl := Real.log_two_gt_d9
  nlinarith

set_option maxHeartbeats 1000000 in
/-- No nonnegative parameter makes the h equals two bound reach the half exponent target. -/
theorem h2_GRH_all_parameters_insufficient125 {t : ℝ} (ht : 0 ≤ t) :
    t * 0.7163436 - Real.log (twoBlockFactor t) / 2 < (1 / 2 : ℝ) * Real.log 2 := by
  have hh := log_twoBlockFactor_tangent125 (r := 5 / 2) (by norm_num) t
  rw [twoBlockFactor_log (by norm_num : (0 : ℝ) < 5 / 2)] at hh
  norm_num at hh
  have hr : Real.log (5 / 2 : ℝ) < 0.917 := by
    have h := Real.sum_range_sub_log_div_le (x := (3 / 7 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ] at h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    linarith
  have hF : (0.699 : ℝ) < Real.log (161 / 80) := by
    have h := Real.sum_range_sub_log_div_le (x := (81 / 241 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ] at h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    linarith
  have hl := Real.log_two_gt_d9
  nlinarith

#print axioms log_twoBlockFactor_tangent125
#print axioms h2_uncond_all_parameters_insufficient125
#print axioms h2_GRH_all_parameters_insufficient125

end LeanLab.PlattTrudgian2014
