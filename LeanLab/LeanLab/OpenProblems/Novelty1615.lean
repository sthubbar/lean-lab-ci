import LeanLab.OpenProblems.Erdos273

/-!
# Erdős 273, Novelty1615: lower bounds on the lcm of a covering

AI wrote this Lean code. Erdős 273 is OPEN and nothing here touches it. Tag: IMPROVEMENT only, a
finite consequence of `one_le_sum_inv`, the reciprocal test. Nothing here is ORIGINAL. If no covering
exists, every statement below is vacuous at `lo = 5`, so `lcmBound_vacuity` shows the hypotheses at
`lo = 3`, where Selfridge's covering satisfies them.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- Every covering with distinct moduli `p - 1`, `p ≥ lo`, has lcm at least `B`.
Twin: a lower bound on the lcm of the moduli. Source: www.erdosproblems.com/forum/thread/273, as quoted in the
novelty report OpenProblems-deepseek-20261103T1237Z section 1.4. -/
def LcmBound (lo B : ℕ) : Prop :=
  ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
    (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ lo ≤ p ∧ s.1 = p - 1) → B ≤ S.lcm Prod.fst

/-- Vacuity instance: Selfridge's covering meets the hypotheses at `lo = 3`. -/
theorem lcmBound_vacuity : ∃ S : Finset (ℕ × ℤ), Covers S ∧ Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) ∧
    ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ s.1 = p - 1 := cover_three

/-- **OPEN target.** Twin: the same bound at 8000000. This is an unrefereed public search, unit U-1615
reproduced only its candidate counts 213 and 420, not the search itself. No Lean proof exists. -/
theorem lcm_ge_8000000 : LcmBound 5 8000000 := by
  sorry

end LeanLab.OpenProblems.Novelty1615
