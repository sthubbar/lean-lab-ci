/-
Split of LeanLab/DtRS1998/Decomp270b, theorem certificate220.

The theorem asks for one finite object: a list of at most 222 primes such that
every even number 10^220 + 2 * j with j < 10^9 / 2 + 1 is the sum of one member
of the list and a prime.  The split cuts the offset range at its middle.  Each
half asks for its own list, its own share of the length budget, and the coverage
test on its own half of the offsets.  The assembly concatenates the two lists,
and the three parts of the claim then transfer: the concatenation has the sum of
the two lengths, it consists of primes as soon as both halves do, and its
coverage test holds at an offset as soon as one of the two lists covers that
offset.  The two halves are the hard steps; the assembly is only their
combination.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- Splitting the offset list `List.range N` at `N1 ≤ N` into its first `N1`
entries and the rest. -/
private theorem range_split220 (N N1 : ℕ) (h : N1 ≤ N) :
    List.range N = List.range N1 ++ (List.range N).drop N1 := by
  have hs := List.take_append_drop N1 (List.range N)
  rw [List.take_range, Nat.min_eq_left h] at hs
  exact hs.symm

/-- A list covering the first `N1` offsets and a list covering the remaining
ones together cover all `N` offsets: the coverage test of the concatenation
holds at every offset where one of the two tests holds. -/
private theorem cover_append220 (B N N1 : ℕ) (hN : N1 ≤ N) (q1 q2 : List ℕ)
    (h1 : (List.range N1).all (fun j => q1.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true)
    (h2 : ((List.range N).drop N1).all (fun j => q2.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) :
    (List.range N).all (fun j => (q1 ++ q2).any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro j hj
  rw [range_split220 N N1 hN, List.mem_append] at hj
  rw [List.any_append, Bool.or_eq_true]
  rcases hj with h | h
  · exact Or.inl (h1 j h)
  · exact Or.inr (h2 j h)

/-- LEAF. Step 1 of the proof, the lower half of the offset range: a list of at
most 111 primes such that for every `j` in `List.range (10 ^ 9 / 4 + 1)`, i.e.
for every `j ≤ 10 ^ 9 / 4`, one member `q` of the list satisfies
`q ≤ 10 ^ 220 + 2 * j` and `10 ^ 220 + 2 * j - q` is prime.  The primality of
each member and of each difference is what the test decides; no ordering of the
list is assumed. -/
theorem certificate220_lower_half :
    ∃ qs : List ℕ, qs.length ≤ 111 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 4 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Step 2 of the proof, the upper half of the offset range: a list of at
most 111 primes that covers every offset of `List.range (10 ^ 9 / 2 + 1)` left
after the first `10 ^ 9 / 4 + 1` are dropped, that is every `j` with
`10 ^ 9 / 4 < j ≤ 10 ^ 9 / 2`, in the same sense as the lower half.  No
ordering of the list is assumed. -/
theorem certificate220_upper_half :
    ∃ qs : List ℕ, qs.length ≤ 111 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ((List.range (10 ^ 9 / 2 + 1)).drop (10 ^ 9 / 4 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- The two half certificates together give the whole one: concatenating their
lists keeps the length within 222, keeps every member prime, and keeps the
coverage on all `10 ^ 9 / 2 + 1` offsets. -/
theorem certificate220_split :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  obtain ⟨q1, hlen1, hpr1, hchk1⟩ := certificate220_lower_half
  obtain ⟨q2, hlen2, hpr2, hchk2⟩ := certificate220_upper_half
  refine ⟨q1 ++ q2, ?_, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hpr1 q h
    · exact hpr2 q h
  · exact cover_append220 (10 ^ 220) (10 ^ 9 / 2 + 1) (10 ^ 9 / 4 + 1)
      (by norm_num) q1 q2 hchk1 hchk2

#print axioms certificate220_split

end LeanLab.DtRS1998.Decomp270b
