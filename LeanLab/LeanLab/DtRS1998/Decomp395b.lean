/-
AI wrote this Lean code for CODEX task395.
P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
These leaves split the existing fixed candidate primality obligation.
All interval coverage proofs and data definitions are reused unchanged.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372bData

namespace LeanLab.DtRS1998.Decomp395b

open Decomp372b

set_option maxRecDepth 100000

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
The four primality batches contain 64, 64, 64 and 15 candidates.
Every batch is nonempty and strictly shorter than the target list. -/
theorem batch_lengths :
    (qs.take 64).length = 64 ∧
    ((qs.drop 64).take 64).length = 64 ∧
    ((qs.drop 128).take 64).length = 64 ∧
    (qs.drop 192).length = 15 := by decide +kernel

/-- P0037 Section 5.1 page 211 and Table 1 page 213.
One explicit member of each batch makes every membership premise inhabited. -/
theorem batch_members :
    (10 ^ 95 - 64011) ∈ qs.take 64 ∧
    (10 ^ 95 - 52373) ∈ (qs.drop 64).take 64 ∧
    (10 ^ 95 - 39417) ∈ (qs.drop 128).take 64 ∧
    (10 ^ 95 - 23171) ∈ qs.drop 192 := by decide +kernel

/-- P0037 Section 5.1 page 211 and Table 1 page 213.
Each batch omits a displayed member of the complete target list.
Together with batch_members this certifies strict smaller subproblems. -/
theorem batch_omissions :
    (10 ^ 95 - 52373) ∈ qs ∧ (10 ^ 95 - 52373) ∉ qs.take 64 ∧
    (10 ^ 95 - 64011) ∈ qs ∧ (10 ^ 95 - 64011) ∉ (qs.drop 64).take 64 ∧
    (10 ^ 95 - 64011) ∉ (qs.drop 128).take 64 ∧ (10 ^ 95 - 64011) ∉ qs.drop 192 := by
  decide +kernel

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95.
Batch 1 of the existing fixed candidate list consists of primes.
This is only the primality subproblem at positions 1 through 64.
Cohen and Lenstra 1987 page 104 separates each candidate test.
The required individual prime certificates remain OPEN. -/
theorem batch0_prime : ∀ q ∈ qs.take 64, q.Prime := by
  sorry

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95.
Batch 2 of the existing fixed candidate list consists of primes.
This is only the primality subproblem at positions 65 through 128.
Cohen and Lenstra 1987 page 104 separates each candidate test.
The required individual prime certificates remain OPEN. -/
theorem batch1_prime : ∀ q ∈ (qs.drop 64).take 64, q.Prime := by
  sorry

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95.
Batch 3 of the existing fixed candidate list consists of primes.
This is only the primality subproblem at positions 129 through 192.
Cohen and Lenstra 1987 page 104 separates each candidate test.
The required individual prime certificates remain OPEN. -/
theorem batch2_prime : ∀ q ∈ (qs.drop 128).take 64, q.Prime := by
  sorry

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95.
Batch 4 of the existing fixed candidate list consists of primes.
This is only the primality subproblem at positions 193 through 207.
Cohen and Lenstra 1987 page 104 separates each candidate test.
The required individual prime certificates remain OPEN. -/
theorem batch3_prime : ∀ q ∈ qs.drop 192, q.Prime := by
  sorry

/-- P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
CONDITIONAL ON the four OPEN finite prime batches.
This is the exact statement of Decomp372b.candidate_primes.
The assembly has no sorry of its own. -/
theorem candidate_primes : ∀ q ∈ qs, q.Prime := by
  intro q hq
  rw [← List.take_append_drop 64 qs, List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch0_prime q hq
  rw [← List.take_append_drop 64 (qs.drop 64), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch1_prime q hq
  simp only [List.drop_drop] at hq
  rw [← List.take_append_drop 64 (qs.drop 128), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch2_prime q hq
  simp only [List.drop_drop] at hq
  exact batch3_prime q hq

#print axioms batch_lengths
#print axioms batch_members
#print axioms batch_omissions
#print axioms batch0_prime
#print axioms batch1_prime
#print axioms batch2_prime
#print axioms batch3_prime
#print axioms candidate_primes

end LeanLab.DtRS1998.Decomp395b
