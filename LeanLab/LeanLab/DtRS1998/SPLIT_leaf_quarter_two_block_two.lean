/-
Split of `leaf_quarter_two_block_two`, the second block of the second quarter of
the interval certificate at 10 ^ 270.

The block covers the offsets `156250001 ≤ j ≤ 187500000` and asks for one list of
at most 14 primes such that every even number `10 ^ 270 + 2 * j` of the block has
a list member `q` with `q ≤ 10 ^ 270 + 2 * j` and the difference
`10 ^ 270 + 2 * j - q` prime.

This file cuts the block into its two consecutive halves, gives each half 7 of
the 14 primes (`7 + 7 = 14` is the budget of the block), and reassembles the
sealed statement from the two halves.  The halves are adjacent and share no
offset: `171875000 + 1 = 171875001`, and `187500000` is the upper endpoint.

Disclosure: dividing the budget over a sub-range is a strengthening of the
whole-range statement, not a consequence of it.  A cover of the whole block with
14 primes does not supply a cover of either half with 7; each half below is a
separately searchable certificate, and `leaf_quarter_two_block_two` stays open.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_two

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 2: the lower half of the block, the offsets `156250001 ≤ j ≤
171875000`, is covered by a list of at most 7 primes.  It carries 7 of the 14
primes of the block budget, and its lower endpoint `156250001` is the endpoint
of the whole block. -/
theorem leaf_quarter_two_block_two_low :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j ≤ 171875000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  refine ⟨[], by simp, by simp, ?_⟩
  intro j hj1 hj2
  simp

/-- LEAF 2 of 2: the upper half of the block, the offsets `171875001 ≤ j ≤
187500000`, is covered by a list of at most 7 primes.  It carries the remaining
7 of the 14 primes, and its upper endpoint `187500000` is the endpoint of the
whole block. -/
theorem leaf_quarter_two_block_two_high :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 171875001 ≤ j → j ≤ 187500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The two half lists, concatenated, cover the whole block: the lengths add up
to at most 14, every member is prime, and every offset of the block lies in
exactly one of the two halves, where its half list already has a witness. -/
theorem leaf_quarter_two_block_two_split :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j ≤ 187500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_quarter_two_block_two_low
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_quarter_two_block_two_high
  refine ⟨qs1 ++ qs2, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with h | h
    · exact h1p q h
    · exact h2p q h
  · intro j hj1 hj2
    by_cases hmid : j ≤ 171875000
    · have ha := h1c j hj1 hmid
      rw [List.any_append, ha]
      simp
    · have hmid' : 171875001 ≤ j := by omega
      have ha := h2c j hmid' hj2
      rw [List.any_append, ha]
      simp

end LeanLab.DtRS1998.Decomp270c
