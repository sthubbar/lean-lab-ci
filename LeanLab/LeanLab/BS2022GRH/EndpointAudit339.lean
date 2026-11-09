/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Audit of the endpoint exponent on journal pp. 1234, 1235 and 1241.
This is a QUESTION about a scalar route and does not refute the finite remainder.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Cutoff339

namespace LeanLab.BS2022GRH.EndpointAudit339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The endpoint power increases throughout the allowed small A band.
This is the power factor in Theorem 7 p. 1235, before its remaining mbar factor. -/
theorem endpoint_power_growth (A X N : ℝ) (hA : A < 4) (hX : 1 < X) (hXN : X < N) :
    log X ^ (4 - A) < log N ^ (4 - A) := by
  exact rpow_lt_rpow (log_pos hX).le
    (log_lt_log (by linarith : 0 < X) hXN) (by linarith)

/-- The paper's complete elementary parameter guards permit A equal to one.
Journal p. 1234 display 25. No GRH or sieve witness is asserted. -/
theorem small_A_conditions : Cond25 (1 / 32) 1 400 (exp (exp 10)) := by
  have hbig : (20000 : ℝ) ≤ exp 10 := by
    have he : exp (10 : ℝ) = exp 1 ^ (10 : ℕ) := by rw [← exp_nat_mul]; norm_num
    rw [he]
    calc (20000 : ℝ) ≤ (2.7 : ℝ) ^ (10 : ℕ) := by norm_num
      _ ≤ exp 1 ^ (10 : ℕ) := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
  have heq (a b : ℝ) :
      (exp (exp 10)) ^ a / log (exp (exp 10)) ^ b = exp (a * exp 10 - b * 10) := by
    rw [log_exp, ← exp_mul, ← exp_mul, ← exp_sub]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [log_exp]
    norm_num
    linarith
  · rw [heq]
    exact exp_le_exp.mpr (by nlinarith)
  · rw [heq]
    have hp : (1 : ℝ) ≤ exp ((1 / 48 : ℝ) * exp 10 - (1 + 4 / 3) * 10) :=
      one_le_exp_iff.mpr (by nlinarith)
    linarith

/-- A concrete increasing endpoint power satisfies the source parameter range.
This witnesses the obstruction to treating the power alone as antitone, p. 1241. -/
theorem small_A_power_witness :
    Cond25 (1 / 32) 1 400 (exp (exp 10)) ∧
      (0 : ℝ) < (1 / 32) ∧ (1 / 32 : ℝ) < 1 / 16 ∧
      log (exp (exp 10)) ^ (4 - (1 : ℝ)) <
        log (exp (2 * exp 10)) ^ (4 - (1 : ℝ)) := by
  refine ⟨small_A_conditions, by norm_num, by norm_num, ?_⟩
  apply endpoint_power_growth 1 _ _ (by norm_num : (1 : ℝ) < 4)
    (one_lt_exp_iff.mpr (exp_pos 10))
  apply exp_lt_exp.mpr
  linarith [exp_pos (10 : ℝ)]

/-- The small A issue has an even natural source domain, not just real endpoints.
Journal p. 1234 display 25. The analytic GRH input is not asserted. -/
theorem small_A_natural_domain : ∃ n : ℕ, Even n ∧ exp (exp 10) ≤ (n : ℝ) ∧
    Cond25 (1 / 32) 1 400 (exp (exp 10)) ∧
      (0 : ℝ) < (1 / 32) ∧ (1 / 32 : ℝ) < 1 / 16 ∧
      (0 : ℝ) < (1 / 2) ∧ (1 / 2 : ℝ) < 1 := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  have hX : exp (exp 10) ≤ exp (exp 13.375) :=
    exp_le_exp.mpr (exp_le_exp.mpr (by norm_num))
  exact ⟨n, hev, hX.trans hn, small_A_conditions, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end
end LeanLab.BS2022GRH.EndpointAudit339
#print axioms LeanLab.BS2022GRH.EndpointAudit339.endpoint_power_growth
#print axioms LeanLab.BS2022GRH.EndpointAudit339.small_A_conditions
#print axioms LeanLab.BS2022GRH.EndpointAudit339.small_A_power_witness

#print axioms LeanLab.BS2022GRH.EndpointAudit339.small_A_natural_domain
