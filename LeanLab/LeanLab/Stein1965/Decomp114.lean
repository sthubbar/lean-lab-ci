/-
P0073, Section 3, page 429. Sparse prime basis existence.
AI wrote this Lean code for CODEX task114. Goldbach is open.
The count and the failure-free run remain cited computational inputs.
-/
import LeanLab.SteinStein1965.Distinct

namespace LeanLab.Stein1965.Decomp114

open LeanLab.SteinStein1965

/-- CITED. Page 429: a prime basis of 10576 elements covers the even interval
from 6 through 10^7. This records existence, not an algorithm identification. -/
def SparsePrimeBasisClaim : Prop :=
  ∃ B : List ℕ, B.length = 10576 ∧ B.Nodup ∧
    (∀ p ∈ B, p.Prime ∧ 3 ≤ p ∧ p ≤ 10 ^ 7) ∧
    IsBasisFor B 6 (10 ^ 7)

/-- The prime S-run restricted to the bound used by B on page 429. -/
def basis : List ℕ := ((sPrime 3 (10 ^ 7)).1.filter (· ≤ 10 ^ 7))

/-- LEAF. Page 429, B(3;10^7) = 10576. A finite count, not reverified here. -/
theorem leaf_count : basis.length = 10576 := by
  sorry

/-- LEAF. Pages 428 and 429: the prime S-run has no failures through 10^7.
This computational input is not reverified here. -/
theorem leaf_no_failures : (sPrime 3 (10 ^ 7)).2 = [] := by
  sorry

/-- LEAF. Section 2, equation 2.3, page 427: selected primes remain prime. -/
theorem leaf_primes : ∀ p ∈ basis, p.Prime ∧ 3 ≤ p ∧ p ≤ 10 ^ 7 := by
  intro p hp
  obtain ⟨hmem, hbound⟩ := List.mem_filter.mp hp
  have hprime := sPrime_elems_prime_unconditional 3 (10 ^ 7) p Nat.prime_three hmem
  exact ⟨hprime.1, hprime.2, of_decide_eq_true hbound⟩

/-- LEAF. Section 2, equations 2.2 and 2.3: an uncovered target adds a new element. -/
theorem leaf_distinct : basis.Nodup := by
  exact List.Nodup.filter _ (sPrime_nodup 3 (10 ^ 7) (by decide))

/-- LEAF. Equations 2.1 to 2.3, pages 427 and 428: failure-freedom gives coverage.
This implication does not assume the cited computational leaf. -/
theorem leaf_coverage (h : (sPrime 3 (10 ^ 7)).2 = []) :
    IsBasisFor basis 6 (10 ^ 7) := by
  intro m hm hlo hhi
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    sAlg_basis_of_nil (primeA 3) 3 (nextA 3) (10 ^ 7) h m hm hlo hhi
  refine ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩,
    y, List.mem_filter.mpr ⟨hy, ?_⟩, hxy⟩
  · exact decide_eq_true (by omega)
  · exact decide_eq_true (by omega)

/-- Page 429, sparse prime basis existence, CONDITIONAL ON leaf_count and
leaf_no_failures. The assembly has no sorry. -/
theorem sparsePrimeBasis_assembled : SparsePrimeBasisClaim := by
  exact ⟨basis, leaf_count, leaf_distinct, leaf_primes, leaf_coverage leaf_no_failures⟩

end LeanLab.Stein1965.Decomp114
