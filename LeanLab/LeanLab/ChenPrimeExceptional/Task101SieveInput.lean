/-
AI wrote this Lean code for CODEX task101.
The remaining analytic sieve input in P0039 pages 66 to 67.
This negative result concerns an arbitrary zero sequence, not the paper's sieve weights.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101StrictCutoffs

open Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

/-- The actual Mertens normalization alone does not force a standard sieve evaluation. -/
theorem actual_standard_sieve_zero_fails :
    ¬ Task58.StandardSieveEvaluation
      (fun n => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6))) (fun _ => 0) := by
  intro h
  have h0 : Tendsto (fun n : ℕ => strictInverseEuler ((n : ℝ) ^ ((1 : ℝ) / 6)) * 0)
      atTop (𝓝 0) := by simp
  have he := tendsto_nhds_unique h0 h
  exact (ne_of_lt Task58.standardF3_pos) he

end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.actual_standard_sieve_zero_fails
