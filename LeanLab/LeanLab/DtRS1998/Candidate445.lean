/-
AI wrote this Lean code for CODEX task445.
P0037 page 211 and Table 1 page 213.
Connect the new primary component leaves to the original prime batches.
Every assembly remains CONDITIONAL ON its explicit OPEN inputs.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp427d
import LeanLab.DtRS1998.Decomp445a
import LeanLab.DtRS1998.Decomp445b
import LeanLab.DtRS1998.Decomp445c

namespace LeanLab.DtRS1998.Candidate445.T90

open Decomp372a

/-- P0037 page 211 and Table 1 page 213, row 10^90.
CONDITIONAL ON the four new primary component leaves in Decomp445a.
Reuse the proved bounds and finite trials from Decomp427a.
This is the exact old batch0_prime statement. -/
theorem batch0_prime : ∀ q ∈ qs.take 64, q.Prime := by
  intro q hq
  have hb := Decomp427a.candidate_bounds q hq
  exact Primality427.prime_of_iterate_trials hb.1 hb.2
    (Decomp445a.divisor_residues q hq)
    (List.all_eq_true.mp Decomp427a.trial_checks q hq)

#print axioms batch0_prime

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^90.
CONDITIONAL ON the four new Decomp445a components and three older prime batches.
This is the exact statement of Decomp372a.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch0_prime q hq
  rw [← List.take_append_drop 64 (qs.drop 64), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395a.batch1_prime q hq
  simp only [List.drop_drop] at hq
  rw [← List.take_append_drop 64 (qs.drop 128), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395a.batch2_prime q hq
  simp only [List.drop_drop] at hq
  exact Decomp395a.batch3_prime q hq

#print axioms candidate_primes

end LeanLab.DtRS1998.Candidate445.T90

namespace LeanLab.DtRS1998.Candidate445.T95

open Decomp372b

/-- P0037 page 211 and Table 1 page 213, row 10^95.
CONDITIONAL ON the four new primary component leaves in Decomp445b.
Reuse the proved bounds and finite trials from Decomp427b.
This is the exact old batch0_prime statement. -/
theorem batch0_prime : ∀ q ∈ qs.take 64, q.Prime := by
  intro q hq
  have hb := Decomp427b.candidate_bounds q hq
  exact Primality427.prime_of_iterate_trials hb.1 hb.2
    (Decomp445b.divisor_residues q hq)
    (List.all_eq_true.mp Decomp427b.trial_checks q hq)

#print axioms batch0_prime

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
CONDITIONAL ON the four new Decomp445b components and three older prime batches.
This is the exact statement of Decomp372b.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch0_prime q hq
  rw [← List.take_append_drop 64 (qs.drop 64), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395b.batch1_prime q hq
  simp only [List.drop_drop] at hq
  rw [← List.take_append_drop 64 (qs.drop 128), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395b.batch2_prime q hq
  simp only [List.drop_drop] at hq
  exact Decomp395b.batch3_prime q hq

#print axioms candidate_primes

end LeanLab.DtRS1998.Candidate445.T95

namespace LeanLab.DtRS1998.Candidate445.T100

open Decomp372c

/-- P0037 page 211 and Table 1 page 213, row 10^100.
CONDITIONAL ON the four new primary component leaves in Decomp445c.
Reuse the proved bounds and finite trials from Decomp427c.
This is the exact old batch0_prime statement. -/
theorem batch0_prime : ∀ q ∈ qs.take 64, q.Prime := by
  intro q hq
  have hb := Decomp427c.candidate_bounds q hq
  exact Primality427.prime_of_iterate_trials hb.1 hb.2
    (Decomp445c.divisor_residues q hq)
    (List.all_eq_true.mp Decomp427c.trial_checks q hq)

#print axioms batch0_prime

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^100.
CONDITIONAL ON the four new Decomp445c components and three older prime batches.
This is the exact statement of Decomp372c.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch0_prime q hq
  rw [← List.take_append_drop 64 (qs.drop 64), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395c.batch1_prime q hq
  simp only [List.drop_drop] at hq
  rw [← List.take_append_drop 64 (qs.drop 128), List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp395c.batch2_prime q hq
  simp only [List.drop_drop] at hq
  exact Decomp395c.batch3_prime q hq

#print axioms candidate_primes

end LeanLab.DtRS1998.Candidate445.T100
