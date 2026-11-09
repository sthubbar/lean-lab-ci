/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Concrete scalar domains for Theorem 5, journal pp. 1228 and 1229.
These statements assert neither GRH nor a universal sieve witness. -/
import LeanLab.BS2022GRH.Scalar333
import LeanLab.BS2022GRH.Cert1575Closed

namespace LeanLab.BS2022GRH.Instances333
open Real ChenThresholdGRH DecompC169a

/-- A positive admissible epsilon permits an exactly zero coefficient.
This witnesses the boundary scalar case of Theorem 5 p. 1228. -/
theorem zero_coefficient (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1 / 8) (hε : 0 < ε) :
    0 < (2 * exp eulerMascheroniConstant * log (3 - 8 * α)) /
      (3 * ε * exp (8 * α - 2)) ∧
    lowerCoefficient α ε ((2 * exp eulerMascheroniConstant * log (3 - 8 * α)) /
      (3 * ε * exp (8 * α - 2))) = 0 := by
  have hl : 0 < log (3 - 8 * α) := log_pos (by linarith)
  constructor
  · positivity
  · unfold lowerCoefficient
    field_simp [hε.ne', (exp_pos (8 * α - 2)).ne',
      show 4 - 8 * α ≠ 0 by linarith]
    <;> ring

/-- The positive coefficient regime has the paper's alpha and epsilon domain.
The scalar choice C2 equal to zero is permitted by the sealed sign guard. -/
theorem positive_coefficient : 0 < lowerCoefficient 0.00256 (1 / 8349) 0 := by
  have hl : 0 < log (3 - 8 * (0.00256 : ℝ)) := log_pos (by norm_num)
  unfold lowerCoefficient
  norm_num
  positivity

/-- The zero coefficient case has every elementary guard of the repaired leaf.
The epsilon and condition 19 are the existing checked journal parameter choices.
No GRH or LinearSieveT4 premise is asserted. -/
theorem zero_coefficient_domain : ∃ (C₂ : ℝ) (n : ℕ),
    0 < C₂ ∧ Even n ∧
    epsJ 1500 ≤ (1 / 8349 : ℝ) ∧ 0 < (1 / 8349 : ℝ) ∧ (1 / 8349 : ℝ) < 1 / 63 ∧
    Cond19 0.00256 10 1500 (exp (exp 13.375)) ∧
    (4e18 : ℝ) ≤ exp (exp 13.375) ∧ exp (exp 13.375) ≤ (n : ℝ) ∧
    lowerCoefficient 0.00256 (1 / 8349) C₂ = 0 ∧
    8 * (UNfull n * n / log n ^ 2) * B5J 0.00256 10 (1 / 8349) C₂
      (exp (exp 13.375)) n < (U7153.SA n : ℝ) := by
  let C₂ := (2 * exp eulerMascheroniConstant * log (3 - 8 * (0.00256 : ℝ))) /
    (3 * (1 / 8349) * exp (8 * 0.00256 - 2))
  have hC := zero_coefficient 0.00256 (1 / 8349) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  refine ⟨C₂, n, hC.1, hev, Cert1575.eps1500.le, by norm_num, by norm_num,
    cond19_13375, X2_ranges.1, hn, hC.2, ?_⟩
  have hLX := (EndpointC169.log_endpoint_gt 0.00256 10 1500 _
    (by norm_num) (by norm_num) (by norm_num) cond19_13375 X2_ranges.1).le
  exact Scalar333.target_of_coefficient_nonpos _ _ _ _ _ n X2_ranges.1 hn hLX hC.2.le

end LeanLab.BS2022GRH.Instances333

#print axioms LeanLab.BS2022GRH.Instances333.zero_coefficient
#print axioms LeanLab.BS2022GRH.Instances333.positive_coefficient
#print axioms LeanLab.BS2022GRH.Instances333.zero_coefficient_domain
