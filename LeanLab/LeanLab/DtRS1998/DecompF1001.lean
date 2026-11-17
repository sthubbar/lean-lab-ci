/-
FREE-ms-leanstral task1001, U-2076 20261117T1628Z-1001: SPLIT of table2_row_25.

Target: P0037 Section 5.2 page 212 and Table 2 page 214, row log10 B = 250,
Nq = 231. The prime list and kernel certificates for all 500000001 even offsets
are OPEN. This file splits the index range into four quarters, each with its own
length budget, and assembles the concatenation.

Each LEAF is a sub-statement strictly easier than the whole: a finite check on
one quarter of the index domain with about a quarter of the length budget.
The assembly is a short chain of exact, rw, calc and linarith that concatenates
the four quarter lists.

No leaf restates the whole statement or assumes it.
No cited input is used; the leaves are computational.

SPLIT of `table2_row_25`.
-/
import LeanLab.DtRS1998.Decomp500a

namespace LeanLab.DtRS1998.Decomp500a

open LeanLab Task71.Paper

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Splitting the offset list `List.range N` at `N1 ≤ N` into its first `N1`
entries and the rest. -/
private theorem range_split (N N1 : ℕ) (h : N1 ≤ N) :
    List.range N = List.range N1 ++ (List.range N).drop N1 := by
  have hs := List.take_append_drop N1 (List.range N)
  rw [List.take_range, Nat.min_eq_left h] at hs
  exact hs.symm

/-- A list covering the first `N1` offsets and a list covering the remaining
ones together cover all `N` offsets: the coverage test of the concatenation
holds at every offset where one of the two tests holds. -/
private theorem cover_append (B N N1 : ℕ) (hN : N1 ≤ N) (q1 q2 : List ℕ)
    (h1 : (List.range N1).all (fun j => q1.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true)
    (h2 : ((List.range N).drop N1).all (fun j => q2.any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) :
    (List.range N).all (fun j => (q1 ++ q2).any (fun q => decide
      (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro j hj
  rw [range_split N N1 hN, List.mem_append] at hj
  rw [List.any_append, Bool.or_eq_true]
  rcases hj with h | h
  · exact Or.inl (h1 j h)
  · exact Or.inr (h2 j h)

/-- LEAF: quarter one, indices 0 to 124999999. A list of at most 58 primes
covers every offset 10^250 + 2*j for j in this range. -/
theorem F1001_quarter_first :
    ∃ qs : List ℕ, qs.length ≤ 58 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 125000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF: quarter two, indices 125000000 to 249999999. A list of at most 58 primes
covers every offset 10^250 + 2*j for j in this range. -/
theorem F1001_quarter_second :
    ∃ qs : List ℕ, qs.length ≤ 58 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000000 ≤ j → j < 250000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF: quarter three, indices 250000000 to 374999999. A list of at most 58 primes
covers every offset 10^250 + 2*j for j in this range. -/
theorem F1001_quarter_third :
    ∃ qs : List ℕ, qs.length ≤ 58 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000000 ≤ j → j < 375000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF: quarter four, indices 375000000 to 499999999. A list of at most 57 primes
covers every offset 10^250 + 2*j for j in this range. -/
theorem F1001_quarter_fourth :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000000 ≤ j → j < 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The assembly: concatenate the four quarter lists. The total length is
58 + 58 + 58 + 57 = 231. Primality is inherited entry by entry. The
coverage test holds at every index j because one of the four quarters covers it. -/
theorem table2_row_25_F1001 :
    ∃ qs : List ℕ, qs.length ≤ 231 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime))) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := F1001_quarter_first
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := F1001_quarter_second
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := F1001_quarter_third
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := F1001_quarter_fourth
  refine ⟨(a₁ ++ a₂) ++ (a₃ ++ a₄), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with h | h
      · exact h₁pr q h
      · exact h₂pr q h
    · rcases hq with h | h
      · exact h₃pr q h
      · exact h₄pr q h
  · have hK : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
    rw [hK, List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rcases Nat.lt_or_ge j 125000000 with h1 | h1
    · have hstep := h₁c j h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · rcases Nat.lt_or_ge j 250000000 with h2 | h2
      · have hstep := h₂c j h1 h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · rcases Nat.lt_or_ge j 375000000 with h3 | h3
        · have hstep := h₃c j h2 h3
          simp only [List.any_append]
          simp only [hstep]
          simp
        · have hstep := h₄c j h3 (by omega)
          simp only [List.any_append]
          simp only [hstep]
          simp

#print axioms table2_row_25_F1001

end LeanLab.DtRS1998.Decomp500a
