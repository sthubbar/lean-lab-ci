/-
Split of the open certificate leaf certificate230 of
LeanLab.DtRS1998.Decomp270b into three smaller finite coverage leaves.

The sealed statement asks for one prime list of at most 228 primes, all at most
10 ^ 230, such that every even offset 10 ^ 230 + 2 * j with j in
[0, 10 ^ 9 / 2] is the sum of a prime from that list and a prime.  The split
cuts the offset range into three consecutive blocks, asks for a separate list of
at most 76 primes for each block, and concatenates the three lists: the offsets
covered by a block are still covered after concatenation, the length bounds add
up to 76 + 76 + 76 = 228, and primality is inherited elementwise.

The three leaves are strictly weaker than the sealed statement: each one covers
a proper sub-block of the offsets and needs at most a third of the primes.

Written for OMOS lomos, unit DtRS1998/SPLIT-certificate230.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF. Step 1 of 3 of the finite coverage certificate: the low block of the
offset range, j from 0 to 10 ^ 8 - 1 (10 ^ 8 offsets).  Some list of at most 76
primes covers every even offset 10 ^ 230 + 2 * j in that block.  No ordering of
the list is assumed, and the list is not required to be disjoint from the lists
of the other two blocks.  This is a strictly smaller piece of the sealed
statement: one fifth of the offsets and a third of the primes. -/
theorem certificate230_block_low :
    ∃ qs : List ℕ, qs.length ≤ 76 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range 100000000).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Step 2 of 3 of the finite coverage certificate: the middle block of the
offset range, the 10 ^ 8 offsets 10 ^ 230 + 2 * (10 ^ 8 + i) for i below 10 ^ 8.
Some list of at most 76 primes covers them.  The block is indexed from 10 ^ 8 so
that the three block statements concatenate without overlap. -/
theorem certificate230_block_mid :
    ∃ qs : List ℕ, qs.length ≤ 76 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range 100000000).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * (100000000 + i) ∧
            (10 ^ 230 + 2 * (100000000 + i) - q).Prime))) = true := by
  sorry

/-- LEAF. Step 3 of 3 of the finite coverage certificate: the high block of the
offset range, the 3 * 10 ^ 8 + 1 offsets 10 ^ 230 + 2 * (2 * 10 ^ 8 + i) for i at
most 3 * 10 ^ 8.  Some list of at most 76 primes covers them.  Together with the
low and middle blocks this exhausts j in [0, 10 ^ 9 / 2] because
10 ^ 8 + 10 ^ 8 + (3 * 10 ^ 8 + 1) = 10 ^ 9 / 2 + 1. -/
theorem certificate230_block_high :
    ∃ qs : List ℕ, qs.length ≤ 76 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range 300000001).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * (200000000 + i) ∧
            (10 ^ 230 + 2 * (200000000 + i) - q).Prime))) = true := by
  sorry

/-- A Boolean any-check of the left list survives appending a second list. -/
private theorem any_append_of_left {α : Type} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  rfl

/-- A Boolean any-check of the right list survives appending it to a first list. -/
private theorem any_append_of_right {α : Type} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₂.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h, Bool.or_true]

/-- The sealed statement of certificate230, assembled from the three block
leaves: concatenate the three prime lists, add the length bounds, keep primality
elementwise, and split the range check at 10 ^ 8 and 2 * 10 ^ 8. -/
theorem certificate230_split :
    ∃ qs : List ℕ, qs.length ≤ 228 ∧ (∀ q ∈ qs, q.Prime) ∧ (List.range (10 ^ 9 / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime))) = true := by
  obtain ⟨qs₁, hlen₁, hpr₁, hchk₁⟩ := certificate230_block_low
  obtain ⟨qs₂, hlen₂, hpr₂, hchk₂⟩ := certificate230_block_mid
  obtain ⟨qs₃, hlen₃, hpr₃, hchk₃⟩ := certificate230_block_high
  have hN : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
  refine ⟨qs₁ ++ (qs₂ ++ qs₃), ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hpr₁ q h
    rcases List.mem_append.mp h with h | h
    · exact hpr₂ q h
    · exact hpr₃ q h
  · refine List.all_eq_true.mpr (fun j hj => ?_)
    have hjlt : j < 500000001 := by
      have h := List.mem_range.mp hj
      rwa [hN] at h
    rcases lt_or_ge j 100000000 with h₁ | h₁
    · exact any_append_of_left (l₁ := qs₁) (l₂ := qs₂ ++ qs₃)
        (List.all_eq_true.mp hchk₁ j (List.mem_range.mpr h₁))
    · rcases lt_or_ge j 200000000 with h₂ | h₂
      · have hi : j - 100000000 < 100000000 := by omega
        have h := List.all_eq_true.mp hchk₂ (j - 100000000) (List.mem_range.mpr hi)
        have he : 100000000 + (j - 100000000) = j := by omega
        rw [he] at h
        exact any_append_of_right (l₁ := qs₁) (l₂ := qs₂ ++ qs₃)
          (any_append_of_left (l₁ := qs₂) (l₂ := qs₃) h)
      · have hi : j - 200000000 < 300000001 := by omega
        have h := List.all_eq_true.mp hchk₃ (j - 200000000) (List.mem_range.mpr hi)
        have he : 200000000 + (j - 200000000) = j := by omega
        rw [he] at h
        exact any_append_of_right (l₁ := qs₁) (l₂ := qs₂ ++ qs₃)
          (any_append_of_right (l₁ := qs₂) (l₂ := qs₃) h)

#print axioms certificate230_split

end LeanLab.DtRS1998.Decomp270b
