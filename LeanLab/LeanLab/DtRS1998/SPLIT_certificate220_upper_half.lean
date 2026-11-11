/-
Split of LeanLab/DtRS1998/SPLIT_certificate220, theorem certificate220_upper_half.

The parent asks for one finite object: a list of at most 111 primes such that every
even number 10^220 + 2 * j whose offset j lies in the upper half,
10^9 / 4 < j <= 10^9 / 2, is the sum of one member of the list and a prime.  This
file cuts the offset range of the upper half at its middle, at 3 * 10^9 / 8 + 1.
Each of the two leaves asks for its own list, its own share of the 111, and the
coverage test on its own sub-range.  The assembly concatenates the two lists: the
concatenation has the sum of the two lengths, it consists of primes as soon as both
halves do, and its coverage test holds at an offset as soon as one of the two lists
covers that offset.  The two halves are the hard steps; the assembly is only their
combination.

Note for the reader: cutting the offset range and the length budget together is not
implied by the parent statement.  The shift count of a covering certificate is set by
the density of the covered offsets, not by the length of the range, so a sub-range
with a proportional share of the budget can need more shifts than it is given.  The
two leaves below are therefore parallel targets, each of the same shape as the
parent, not consequences of it.
-/
import LeanLab.DtRS1998.SPLIT_certificate220

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- The offset list of the upper half, `(List.range N).drop N0`, cut at an index
`M` between `N0` and `N`: the entries before `M` followed by the entries from `M`
on.  The first part is the same list read off `List.range M`. -/
private theorem drop_split220uh (N N0 M : ℕ) (h0 : N0 ≤ M) (hMN : M ≤ N) :
    (List.range N).drop N0 = ((List.range M).drop N0) ++ ((List.range N).drop M) := by
  have h1 : N0 + (M - N0) = M := by omega
  rw [← List.drop_take_append_drop (List.range N) N0 (M - N0), h1]
  rw [List.take_drop, h1, List.take_range, Nat.min_eq_left hMN]

/-- A list covering the first sub-range and a list covering the second one together
cover the whole range: the coverage test of the concatenation holds at every offset
at which one of the two tests holds. -/
private theorem cover_append220uh (B N0 M N : ℕ) (h0 : N0 ≤ M) (hMN : M ≤ N)
    (q1 q2 : List ℕ)
    (h1 : ((List.range M).drop N0).all (fun j => q1.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true)
    (h2 : ((List.range N).drop M).all (fun j => q2.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) :
    ((List.range N).drop N0).all (fun j => (q1 ++ q2).any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro j hj
  rw [drop_split220uh N N0 M h0 hMN, List.mem_append] at hj
  rw [List.any_append, Bool.or_eq_true]
  rcases hj with h | h
  · exact Or.inl (h1 j h)
  · exact Or.inr (h2 j h)

/-- LEAF. Step 1 of the proof, the lower sub-range of the upper half: a list of at
most 56 primes such that for every offset `j` of `List.range (3 * 10 ^ 9 / 8 + 1)`
left after the first `10 ^ 9 / 4 + 1` are dropped, that is every `j` with
`10 ^ 9 / 4 < j <= 3 * 10 ^ 9 / 8`, one member `q` of the list satisfies
`q ≤ 10 ^ 220 + 2 * j` and `10 ^ 220 + 2 * j - q` is prime.  The primality of each
member and of each difference is what the test decides; no ordering of the list is
assumed. -/
theorem certificate220_upper_first_half :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ((List.range (3 * 10 ^ 9 / 8 + 1)).drop (10 ^ 9 / 4 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Step 2 of the proof, the upper sub-range of the upper half: a list of at
most 55 primes that covers every offset of `List.range (10 ^ 9 / 2 + 1)` left after
the first `3 * 10 ^ 9 / 8 + 1` are dropped, that is every `j` with
`3 * 10 ^ 9 / 8 < j <= 10 ^ 9 / 2`, in the same sense as the lower sub-range.  No
ordering of the list is assumed. -/
theorem certificate220_upper_second_half :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ((List.range (10 ^ 9 / 2 + 1)).drop (3 * 10 ^ 9 / 8 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- The two sub-range certificates together give the upper half certificate:
concatenating their lists keeps the length within 111, keeps every member prime, and
keeps the coverage on every offset of the upper half. -/
theorem certificate220_upper_half_split :
    ∃ qs : List ℕ, qs.length ≤ 111 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ((List.range (10 ^ 9 / 2 + 1)).drop (10 ^ 9 / 4 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  obtain ⟨q1, hlen1, hpr1, hchk1⟩ := certificate220_upper_first_half
  obtain ⟨q2, hlen2, hpr2, hchk2⟩ := certificate220_upper_second_half
  refine ⟨q1 ++ q2, ?_, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hpr1 q h
    · exact hpr2 q h
  · exact cover_append220uh (10 ^ 220) (10 ^ 9 / 4 + 1) (3 * 10 ^ 9 / 8 + 1)
      (10 ^ 9 / 2 + 1) (by norm_num) (by norm_num) q1 q2 hchk1 hchk2

#print axioms certificate220_upper_half_split

end LeanLab.DtRS1998.Decomp270b
