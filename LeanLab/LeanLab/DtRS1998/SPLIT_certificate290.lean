/-
Split of certificate290 into two half-domain finite coverage leaves.

The whole obligation asks for a list of at most 226 primes q with
q <= 10^290 + 2 * j and 10^290 + 2 * j - q prime, for every j with
0 <= j <= 10^9 / 2, that is 500000001 values of j.

This file splits the index domain into two consecutive blocks:

  block one   0 <= j < 250000001          (250000001 values)
  block two   250000001 <= j < 500000001  (250000000 values)

and asks for a separate covering list of at most 113 primes for each block.
The two lists are concatenated, so the two length bounds add up to
2 * 113 = 226, which is exactly the budget of the obligation, and the two
block checks are combined by one elementary concatenation step on List.all
over List.range.

Each leaf is a finite verification over half of the index domain with half
of the length budget, hence strictly easier than the whole obligation, and
no leaf assumes or restates it.

The private result below is fully proved, and the assembly
certificate290_split is proved outright from the two leaves.
-/
import LeanLab.DtRS1998.Decomp270c

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- Two consecutive blocks of the same Boolean range check, the first on the
indices `0, 1, ..., M - 1` and the second on the indices `M, ..., M + L - 1`
written with the shift `M` made explicit. Together they give the check on the
whole range of `M + L` indices. Stated for the offset predicate of this file
rather than for an arbitrary predicate: the general form forces the elaborator
to beta-reduce a `decide` term carrying `Nat.Prime`, which runs into the
recursion limit. -/
private theorem all_range_link (a : List ℕ) (E M L : ℕ)
    (h1 : (List.range M).all (fun j => a.any (fun q => decide
      (q ≤ E + 2 * j ∧ (E + 2 * j - q).Prime))) = true)
    (h2 : (List.range L).all (fun i => a.any (fun q => decide
      (q ≤ E + 2 * (M + i) ∧ (E + 2 * (M + i) - q).Prime))) = true) :
    (List.range (M + L)).all (fun j => a.any (fun q => decide
      (q ≤ E + 2 * j ∧ (E + 2 * j - q).Prime))) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro j hj
  rw [List.mem_range] at hj
  rcases Nat.lt_or_ge j M with hlt | hge
  · exact h1 j (List.mem_range.mpr hlt)
  · have hsub : j - M < L := by omega
    have hstep := h2 (j - M) (List.mem_range.mpr hsub)
    have hje : M + (j - M) = j := by omega
    rwa [hje] at hstep

/-- LEAF: Block one of the split index range: the offsets 10^290 + 2 * j
for 0 <= j < 250000001 are covered by one list of at most 113 primes. This
is the prime list and the finite offset check for the first half of the
index domain, with half of the total length budget. -/
theorem leaf_block_one :
    ∃ qs : List ℕ, qs.length ≤ 113 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 250000001).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 290 + 2 * j ∧ (10 ^ 290 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF: Block two of the split index range: the offsets 10^290 + 2 * j
for 250000001 <= j < 500000001 are covered by one list of at most 113
primes, written here with the block offset as the variable i. This is the
prime list and the finite offset check for the second half of the index
domain, with half of the total length budget. -/
theorem leaf_block_two :
    ∃ qs : List ℕ, qs.length ≤ 113 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 250000000).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 290 + 2 * (250000001 + i) ∧
            (10 ^ 290 + 2 * (250000001 + i) - q).Prime))) = true := by
  sorry

/-- The whole certificate, proved from the two half-domain leaves: the two
lists concatenate, their length bounds add up to 226, primality is inherited
entry by entry, and the two offset checks cover the whole index domain
through the concatenation step. -/
theorem certificate290_split :
    ∃ qs : List ℕ, qs.length ≤ 226 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 290 + 2 * j ∧ (10 ^ 290 + 2 * j - q).Prime))) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_block_one
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_block_two
  refine ⟨a₁ ++ a₂, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    rw [List.mem_append] at hq
    rcases hq with h | h
    · exact h₁pr q h
    · exact h₂pr q h
  · -- the first block, with the second block's list appended
    have hq₁ : (List.range 250000001).all (fun j => (a₁ ++ a₂).any (fun q => decide
        (q ≤ 10 ^ 290 + 2 * j ∧ (10 ^ 290 + 2 * j - q).Prime))) = true := by
      rw [List.all_eq_true] at h₁c ⊢
      intro j hj
      have hstep := h₁c j hj
      rw [List.any_append, hstep]
      exact Bool.true_or _
    -- the second block, with the first block's list prepended
    have hq₂ : (List.range 250000000).all (fun i => (a₁ ++ a₂).any (fun q => decide
        (q ≤ 10 ^ 290 + 2 * (250000001 + i) ∧
          (10 ^ 290 + 2 * (250000001 + i) - q).Prime))) = true := by
      rw [List.all_eq_true] at h₂c ⊢
      intro i hi
      have hstep := h₂c i hi
      rw [List.any_append, hstep]
      exact Bool.or_true _
    have hK : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
    rw [hK]
    exact all_range_link (a₁ ++ a₂) (10 ^ 290) 250000001 250000000 hq₁ hq₂


end LeanLab.DtRS1998.Decomp270c
