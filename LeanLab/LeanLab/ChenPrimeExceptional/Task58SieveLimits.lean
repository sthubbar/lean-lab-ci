/-
AI wrote this Lean code for CODEX task58.
The normalization limit underlying the source check on P0039 pages 66 to 67.
The Mertens and linear sieve evaluations are named analytic inputs, not proved here.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Normalization

open Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- Named analytic input: the ratio of the two inverse sieve products tends to three fifths. -/
def MertensNormalization (A B : ℕ → ℝ) : Prop :=
  Tendsto (fun n => A n / B n) atTop (𝓝 (3 / 5))

/-- Named analytic input: the larger-cutoff normalization has the standard F of 3 value. -/
def StandardSieveEvaluation (B S : ℕ → ℝ) : Prop :=
  Tendsto (fun n => B n * S n) atTop (𝓝 standardF3)

/-- CONDITIONAL ON the two named analytic limits, the page 66 normalization carries an
additional factor three fifths compared with the standard F of 3 normalization. -/
theorem sieve_normalization_limit {A B S : ℕ → ℝ} (hB : ∀ n, B n ≠ 0)
    (hM : MertensNormalization A B) (hS : StandardSieveEvaluation B S) :
    Tendsto (fun n => A n * S n) atTop (𝓝 page66F3Model) := by
  have h := hM.mul hS
  exact h.congr (fun n => (normalization_change (A := A n) (S := S n) (hB n)).symm)

/-- CONDITIONAL ON the same analytic limits, the page 66 value does not tend to the
standard F of 3 value itself. -/
theorem not_standard_normalization_limit {A B S : ℕ → ℝ} (hB : ∀ n, B n ≠ 0)
    (hM : MertensNormalization A B) (hS : StandardSieveEvaluation B S) :
    ¬ Tendsto (fun n => A n * S n) atTop (𝓝 standardF3) := by
  intro h
  have he := tendsto_nhds_unique (sieve_normalization_limit hB hM hS) h
  exact (ne_of_lt page66F3Model_lt) he

/-- The two named limit inputs are jointly satisfiable. -/
theorem normalization_limits_vacuity :
    MertensNormalization (fun _ => (3 / 5 : ℝ)) (fun _ => 1) ∧
      StandardSieveEvaluation (fun _ => (1 : ℝ)) (fun _ => standardF3) := by
  constructor
  · simpa [MertensNormalization] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 / 5 : ℝ)) atTop (𝓝 (3 / 5)))
  · simpa [StandardSieveEvaluation] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => standardF3) atTop (𝓝 standardF3))

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.sieve_normalization_limit
#print axioms LeanLab.ChenPrimeExceptional.Task58.not_standard_normalization_limit
#print axioms LeanLab.ChenPrimeExceptional.Task58.normalization_limits_vacuity
