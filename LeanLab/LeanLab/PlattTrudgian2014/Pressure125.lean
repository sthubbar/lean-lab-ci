/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 184 display 7.1. These are rational logarithm enclosures and a strict gap.
They do not assert the analytic moment transfer.
-/
import LeanLab.PlattTrudgian2014.Perron125

namespace LeanLab.PlattTrudgian2014

open Finset

set_option maxHeartbeats 1000000 in
theorem log_two_upper125 : Real.log 2 < 0.693147180559946 := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 3 : ℝ)) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).2
  linarith

set_option maxHeartbeats 1000000 in
theorem half_log_radius_upper125 : Real.log (halfRadius125 : ℝ) < 0.296050610228733 := by
  have hr : (halfRadius125 : ℝ) ≤ (1344538202496103214 / 10 ^ 18 : ℝ) := by
    norm_num [halfRadius125]
  have hp : (0 : ℝ) < halfRadius125 := by norm_num [halfRadius125]
  have hm := Real.log_le_log hp hr
  have h := Real.sum_range_sub_log_div_le
    (x := (344538202496103214 / 2344538202496103214 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).2
  linarith

/-- A certified gap above the exact printed half exponent threshold. -/
theorem half_pressure_gap125 :
    Real.log (halfRadius125 : ℝ) + (1 / 2 : ℝ) * Real.log 2 + 0.0000000000006 <
      (halfParameter125 : ℝ) * 0.7163435444776661 := by
  have h1 := log_two_upper125
  have h2 := half_log_radius_upper125
  norm_num [halfParameter125] at *
  linarith

#print axioms log_two_upper125
#print axioms half_log_radius_upper125
#print axioms half_pressure_gap125

end LeanLab.PlattTrudgian2014
