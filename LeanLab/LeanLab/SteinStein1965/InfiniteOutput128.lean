/-
AI wrote this Lean code for CODEX task128.
P0073, Section 2, page 428, the infinite-input S-sequence.
There are infinitely many distinct generated elements. No coverage assertion is made.
Goldbach is open.
-/
import LeanLab.SteinStein1965.PrimeGrowth128
import LeanLab.SteinStein1965.Distinct

namespace LeanLab.SteinStein1965

/-- Page 428: the union of the finite prime-run outputs is infinite. -/
theorem prime_output_infinite128 (p0 : ℕ) (hpos : 1 ≤ p0) :
    Set.Infinite {b : ℕ | ∃ N, b ∈ (sPrime p0 N).1} := by
  classical
  by_contra h
  have hfin : Set.Finite {b : ℕ | ∃ N, b ∈ (sPrime p0 N).1} := Set.not_infinite.mp h
  obtain ⟨N, _, hlen⟩ := prime_output_unbounded128 p0 hpos hfin.toFinset.card
  have hs : (sPrime p0 N).1.toFinset ⊆ hfin.toFinset := by
    intro b hb
    exact hfin.mem_toFinset.mpr ⟨N, List.mem_toFinset.mp hb⟩
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (sPrime_nodup p0 N hpos)] at hc
  omega

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.prime_output_infinite128
