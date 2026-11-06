/-
AI wrote this Lean code for CODEX task427.
P0037 Section 5.1 page 211 and Table 1 page 213.
Connect the new first batch residue splits with the nine older prime batches.
All three list assemblies remain CONDITIONAL ON their OPEN leaves.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp427a
import LeanLab.DtRS1998.Decomp395a
import LeanLab.DtRS1998.Decomp427b
import LeanLab.DtRS1998.Decomp395b
import LeanLab.DtRS1998.Decomp427c
import LeanLab.DtRS1998.Decomp395c

namespace LeanLab.DtRS1998.Decomp427d.T90

open Decomp372a

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^90.
CONDITIONAL ON Decomp427a.divisor_residues and the three older prime batches.
This is the exact statement of Decomp372a.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp427a.batch0_prime q hq
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

end LeanLab.DtRS1998.Decomp427d.T90

namespace LeanLab.DtRS1998.Decomp427d.T95

open Decomp372b

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
CONDITIONAL ON Decomp427b.divisor_residues and the three older prime batches.
This is the exact statement of Decomp372b.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp427b.batch0_prime q hq
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

end LeanLab.DtRS1998.Decomp427d.T95

namespace LeanLab.DtRS1998.Decomp427d.T100

open Decomp372c

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^100.
CONDITIONAL ON Decomp427c.divisor_residues and the three older prime batches.
This is the exact statement of Decomp372c.candidate_primes.
No old first batch prime proof is used. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact Decomp427c.batch0_prime q hq
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

end LeanLab.DtRS1998.Decomp427d.T100
