/-
Split of the fourth fixed candidate batch of row 10^90.
The batch qs.drop 192 carries 17 candidates. It is cut here into four
consecutive sub-batches of 4, 4, 4 and 5 entries. Each sub-batch is one
LEAF; the assembly is only list bookkeeping over the cuts.
The batch is inhabited: batch_members places 10 ^ 90 - 21317 in qs.drop 192.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp395a

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- The fourth batch of the fixed candidate list has 17 entries, so the cut
4 + 4 + 4 + 5 covers it with no entry left over. This is the fourth conjunct of
batch_lengths, restated under a name for the bookkeeping below. -/
private theorem batch3_card : (qs.drop 192).length = 17 := batch_lengths.2.2.2

/-- The four cuts are nonempty: their lengths are 4, 4, 4 and 5. This records
that none of the four leaves below is a statement about an empty list. -/
private theorem batch3_cut_cards :
    ((qs.drop 192).take 4).length = 4 ∧
    (((qs.drop 192).drop 4).take 4).length = 4 ∧
    (((qs.drop 192).drop 8).take 4).length = 4 ∧
    ((qs.drop 192).drop 12).length = 5 := by
  have h : (qs.drop 192).length = 17 := batch3_card
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_take, h]; decide
  · rw [List.length_take, List.length_drop, h]; decide
  · rw [List.length_take, List.length_drop, h]; decide
  · rw [List.length_drop, h]

/-- LEAF. First cut of the fourth batch, positions 193 to 196: the four fixed
candidates qs.drop 192 take 4 are prime. This is the four integer tests of the
first cut only, strictly narrower than the whole batch. -/
theorem batch3_prime_part1 : ∀ q ∈ (qs.drop 192).take 4, q.Prime := by
  sorry

/-- LEAF. Second cut of the fourth batch, positions 197 to 200: the four fixed
candidates (qs.drop 192).drop 4 take 4 are prime. This is the four integer
tests of the second cut only. -/
theorem batch3_prime_part2 : ∀ q ∈ ((qs.drop 192).drop 4).take 4, q.Prime := by
  sorry

/-- LEAF. Third cut of the fourth batch, positions 201 to 204: the four fixed
candidates (qs.drop 192).drop 8 take 4 are prime. This is the four integer
tests of the third cut only. -/
theorem batch3_prime_part3 : ∀ q ∈ ((qs.drop 192).drop 8).take 4, q.Prime := by
  sorry

/-- LEAF. Last cut of the fourth batch, positions 205 to 209: the five fixed
candidates (qs.drop 192).drop 12 are prime. This is the five integer tests of
the tail cut only. -/
theorem batch3_prime_part4 : ∀ q ∈ (qs.drop 192).drop 12, q.Prime := by
  sorry

/-- The fourth fixed candidate batch of row 10^90 consists of primes.
Assembled from the four cut leaves above by re-cutting the list four times;
the proof itself uses no primality beyond the four leaves. -/
theorem batch3_prime_split : ∀ q ∈ qs.drop 192, q.Prime := by
  intro q hq
  have e1 : ((qs.drop 192).drop 4).drop 4 = (qs.drop 192).drop 8 := by
    simp [List.drop_drop]
  have e2 : ((qs.drop 192).drop 8).drop 4 = (qs.drop 192).drop 12 := by
    simp [List.drop_drop]
  rw [← List.take_append_drop 4 (qs.drop 192), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part1 q hq
  rw [← List.take_append_drop 4 ((qs.drop 192).drop 4), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part2 q hq
  rw [e1, ← List.take_append_drop 4 ((qs.drop 192).drop 8), List.mem_append] at hq
  rcases hq with hq | hq
  · exact batch3_prime_part3 q hq
  rw [e2] at hq
  exact batch3_prime_part4 q hq

#print axioms batch3_prime_part1
#print axioms batch3_prime_part2
#print axioms batch3_prime_part3
#print axioms batch3_prime_part4
#print axioms batch3_prime_split

end LeanLab.DtRS1998.Decomp395a
