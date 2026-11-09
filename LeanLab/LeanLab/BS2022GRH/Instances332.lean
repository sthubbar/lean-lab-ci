/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Nonempty scalar endpoint domains for journal pp. 1240 and 1241. -/
import LeanLab.BS2022GRH.EndpointCompare332

namespace LeanLab.BS2022GRH.Instances332
open Real ChenThresholdGRH

/-- The normalized endpoint domain has distinct concrete endpoints at A equal to four.
Derived scalar domain for journal display 33, p. 1241. -/
theorem endpoint_domain :
    0 < exp (22000 : ℝ) ∧ exp (22000 : ℝ) < exp 22001 ∧
      22000 ≤ log (exp (22000 : ℝ)) ∧
      2 * ((4 : ℝ) + 1) ≤ log (exp (22000 : ℝ)) ∧
      1e8 ≤ √(exp (22000 : ℝ)) / log (exp (22000 : ℝ)) ^ ((4 : ℝ) + 1) := by
  have he : (1e8 : ℝ) * 22000 ^ (5 : ℕ) ≤ exp (11000 : ℝ) := by
    have hp := pow_div_factorial_le_exp (x := (11000 : ℝ)) (by norm_num) 10
    norm_num at hp ⊢
    linarith
  have hs : √(exp (22000 : ℝ)) = exp (11000 : ℝ) := by
    rw [sqrt_eq_rpow, ← exp_mul]
    norm_num
  refine ⟨exp_pos _, exp_lt_exp.mpr (by norm_num), by simp, by norm_num, ?_⟩
  rw [hs, log_exp]
  norm_num only [show (4 : ℝ) + 1 = 5 by norm_num, rpow_ofNat]
  convert (le_div_iff₀ (by norm_num : (0 : ℝ) < 22000 ^ (5 : ℕ))).mpr he using 1 <;> norm_num

/-- Display 25 holds at A four, alpha one over 32 and u 400.
This supplies the complete source guards for the restricted endpoint theorem.
Journal pp. 1234 and 1235 display 25 and p. 1241 display 33. -/
theorem source_domain : Cond25 (1 / 32) 4 400 (exp (exp 10)) := by
  have hbig : (22000 : ℝ) ≤ exp 10 := by
    simpa only [log_exp] using Lemma11C164.log_lower (exp (exp 10)) le_rfl
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
    have hp : (1 : ℝ) ≤ exp ((1 / 48 : ℝ) * exp 10 - (4 + 4 / 3) * 10) :=
      one_le_exp_iff.mpr (by nlinarith)
    linarith

/-- The restricted full endpoint inequality applies to distinct source endpoints.
Journal p. 1241 display 33. This asserts no GRH or sieve witness. -/
theorem endpoint_instance :
    DecompC164c.errorBracket 4 (exp (2 * exp 10)) (1 / 2) ≤
      DecompC164c.errorBracket 4 (exp (exp 10)) (1 / 2) := by
  apply EndpointCompare332.error_at_threshold (1 / 32) 4 400 (exp (exp 10))
    (exp (2 * exp 10)) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    source_domain le_rfl
  apply exp_le_exp.mpr
  linarith [exp_pos (10 : ℝ)]

end LeanLab.BS2022GRH.Instances332
#print axioms LeanLab.BS2022GRH.Instances332.endpoint_domain
#print axioms LeanLab.BS2022GRH.Instances332.source_domain
#print axioms LeanLab.BS2022GRH.Instances332.endpoint_instance
