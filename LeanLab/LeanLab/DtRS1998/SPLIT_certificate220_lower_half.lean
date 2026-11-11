/-
Split of LeanLab/DtRS1998/SPLIT_certificate220, theorem certificate220_lower_half.

The parent asks for one finite object: a list of at most 111 primes such that every
even number 10^220 + 2 * j with j < 10^9 / 4 + 1 is the sum of one member of the
list and a prime.  This file cuts the offset range of the lower half at its middle,
at 10^9 / 8 + 1.  Each of the two leaves asks for its own list, its own share of the
111, and the coverage test on its own sub-range.  The assembly concatenates the two
lists: the concatenation has the sum of the two lengths, it consists of primes as
soon as both halves do, and its coverage test holds at an offset as soon as one of
the two lists covers that offset.  The two halves are the hard steps; the assembly
is only their combination.

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

/-- Splitting the offset list `List.range N` at `N1 ≤ N` into its first `N1`
entries and the rest. -/
private theorem range_split220lh (N N1 : ℕ) (h : N1 ≤ N) :
    List.range N = List.range N1 ++ (List.range N).drop N1 := by
  have hs := List.take_append_drop N1 (List.range N)
  rw [List.take_range, Nat.min_eq_left h] at hs
  exact hs.symm

/-- A list covering the first `N1` offsets and a list covering the remaining ones
together cover all `N` offsets: the coverage test of the concatenation holds at
every offset where one of the two tests holds. -/
private theorem cover_append220lh (B N N1 : ℕ) (hN : N1 ≤ N) (q1 q2 : List ℕ)
    (h1 : (List.range N1).all (fun j => q1.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true)
    (h2 : ((List.range N).drop N1).all (fun j => q2.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) :
    (List.range N).all (fun j => (q1 ++ q2).any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro j hj
  rw [range_split220lh N N1 hN, List.mem_append] at hj
  rw [List.any_append, Bool.or_eq_true]
  rcases hj with h | h
  · exact Or.inl (h1 j h)
  · exact Or.inr (h2 j h)

/-- LEAF. Step 1 of the proof, the first half of the lower half of the offset
range: a list of at most 56 primes such that for every `j` in
`List.range (10 ^ 9 / 8 + 1)`, i.e. for every `j ≤ 10 ^ 9 / 8`, one member `q` of
the list satisfies `q ≤ 10 ^ 220 + 2 * j` and `10 ^ 220 + 2 * j - q` is prime.
The primality of each member and of each difference is what the test decides; no
ordering of the list is assumed. -/
theorem certificate220_lower_first_half :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 8 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Step 2 of the proof, the second half of the lower half of the offset
range: a list of at most 55 primes that covers every offset of
`List.range (10 ^ 9 / 4 + 1)` left after the first `10 ^ 9 / 8 + 1` are dropped,
that is every `j` with `10 ^ 9 / 8 < j ≤ 10 ^ 9 / 4`, in the same sense as the
first half.  No ordering of the list is assumed. -/
theorem certificate220_lower_second_half :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ((List.range (10 ^ 9 / 4 + 1)).drop (10 ^ 9 / 8 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- The two halves together give the lower half certificate: concatenating their
lists keeps the length within 111, keeps every member prime, and keeps the
coverage on all `10 ^ 9 / 4 + 1` offsets. -/
theorem certificate220_lower_half_split :
    ∃ qs : List ℕ, qs.length ≤ 111 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 4 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  obtain ⟨q1, hlen1, hpr1, hchk1⟩ := certificate220_lower_first_half
  obtain ⟨q2, hlen2, hpr2, hchk2⟩ := certificate220_lower_second_half
  refine ⟨q1 ++ q2, ?_, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hpr1 q h
    · exact hpr2 q h
  · exact cover_append220lh (10 ^ 220) (10 ^ 9 / 4 + 1) (10 ^ 9 / 8 + 1)
      (by norm_num) q1 q2 hchk1 hchk2

#print axioms certificate220_lower_half_split

end LeanLab.DtRS1998.Decomp270b
