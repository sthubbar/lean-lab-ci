/-
Split of the batch 1 primality obligation of Decomp395a.

Batch 1 is the block of positions 65 through 128 of the fixed row 90 candidate
list `qs`, that is `(qs.drop 64).take 64`. The eight leaves below cut that block
into eight consecutive windows of eight positions each, and the assembly
`batch1_prime_split` reassembles the block from them by splitting the list once
per window. Every leaf is a strictly smaller finite primality obligation than
the whole block; none of them assumes the block statement.
The eight leaves remain OPEN. The assembly has no sorry of its own.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp395a

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- LEAF. First step of the proof of batch 1: the first window of eight
positions of batch 1, namely positions 65 through 72 of the fixed row 90
candidate list, consists of primes. This is the prefix window cut by
`(qs.drop 64).take 8`. The finite primality obligations of these eight
candidates stay OPEN. -/
theorem batch1_part0_prime : ∀ q ∈ (qs.drop 64).take 8, q.Prime := by
  sorry

/-- LEAF. Second step of the proof of batch 1: the second window of eight
positions of batch 1, namely positions 73 through 80, consists of primes.
This is the window `(qs.drop 72).take 8` obtained after removing the first
window. The finite primality obligations of these eight candidates stay OPEN. -/
theorem batch1_part1_prime : ∀ q ∈ (qs.drop 72).take 8, q.Prime := by
  sorry

/-- LEAF. Third step of the proof of batch 1: the third window of eight
positions of batch 1, namely positions 81 through 88, consists of primes.
This is the window `(qs.drop 80).take 8`. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part2_prime : ∀ q ∈ (qs.drop 80).take 8, q.Prime := by
  sorry

/-- LEAF. Fourth step of the proof of batch 1: the fourth window of eight
positions of batch 1, namely positions 89 through 96, consists of primes.
This is the window `(qs.drop 88).take 8`. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part3_prime : ∀ q ∈ (qs.drop 88).take 8, q.Prime := by
  sorry

/-- LEAF. Fifth step of the proof of batch 1: the fifth window of eight
positions of batch 1, namely positions 97 through 104, consists of primes.
This is the window `(qs.drop 96).take 8`. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part4_prime : ∀ q ∈ (qs.drop 96).take 8, q.Prime := by
  sorry

/-- LEAF. Sixth step of the proof of batch 1: the sixth window of eight
positions of batch 1, namely positions 105 through 112, consists of primes.
This is the window `(qs.drop 104).take 8`. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part5_prime : ∀ q ∈ (qs.drop 104).take 8, q.Prime := by
  sorry

/-- LEAF. Seventh step of the proof of batch 1: the seventh window of eight
positions of batch 1, namely positions 113 through 120, consists of primes.
This is the window `(qs.drop 112).take 8`. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part6_prime : ∀ q ∈ (qs.drop 112).take 8, q.Prime := by
  sorry

/-- LEAF. Eighth and last step of the proof of batch 1: the final window of
eight positions of batch 1, namely positions 121 through 128, consists of
primes. This is the window `(qs.drop 120).take 8`, which is all that remains of
the block after the seven earlier windows. The finite primality obligations of
these eight candidates stay OPEN. -/
theorem batch1_part7_prime : ∀ q ∈ (qs.drop 120).take 8, q.Prime := by
  sorry

/-- The exact statement of `batch1_prime`, proved from the eight windows above
and not from `batch1_prime` itself. Each of the seven steps rewrites the
remaining block `(qs.drop (64 + 8 * k)).take (64 - 8 * k)` into its next window
of eight followed by a shorter remainder, using `List.take_add` and
`List.drop_drop`. -/
theorem batch1_prime_split : ∀ q ∈ (qs.drop 64).take 64, q.Prime := by
  intro q hq
  rw [show (64 : ℕ) = 8 + 56 from rfl, List.take_add] at hq
  rcases List.mem_append.mp hq with h | h
  · exact batch1_part0_prime q h
  rw [List.drop_drop, show (64 : ℕ) + 8 = 72 from rfl,
    show (56 : ℕ) = 8 + 48 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part1_prime q h
  rw [List.drop_drop, show (72 : ℕ) + 8 = 80 from rfl,
    show (48 : ℕ) = 8 + 40 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part2_prime q h
  rw [List.drop_drop, show (80 : ℕ) + 8 = 88 from rfl,
    show (40 : ℕ) = 8 + 32 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part3_prime q h
  rw [List.drop_drop, show (88 : ℕ) + 8 = 96 from rfl,
    show (32 : ℕ) = 8 + 24 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part4_prime q h
  rw [List.drop_drop, show (96 : ℕ) + 8 = 104 from rfl,
    show (24 : ℕ) = 8 + 16 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part5_prime q h
  rw [List.drop_drop, show (104 : ℕ) + 8 = 112 from rfl,
    show (16 : ℕ) = 8 + 8 from rfl, List.take_add] at h
  rcases List.mem_append.mp h with h | h
  · exact batch1_part6_prime q h
  rw [List.drop_drop, show (112 : ℕ) + 8 = 120 from rfl] at h
  exact batch1_part7_prime q h

#print axioms batch1_part0_prime
#print axioms batch1_part1_prime
#print axioms batch1_part2_prime
#print axioms batch1_part3_prime
#print axioms batch1_part4_prime
#print axioms batch1_part5_prime
#print axioms batch1_part6_prime
#print axioms batch1_part7_prime
#print axioms batch1_prime_split

end LeanLab.DtRS1998.Decomp395a
