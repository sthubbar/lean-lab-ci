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

/-- The reciprocal-sum route alone cannot prove the bound. These 18 admissible moduli divide
`7650720 < 8000000`, and their reciprocal sum is greater than one. -/
theorem admissible_recip_counterexample_7650720 :
    (∑ m ∈ ({4, 6, 10, 12, 16, 18, 22, 28, 30, 36, 40, 42, 46, 60, 66, 70, 72, 88} : Finset ℕ),
      (1 : ℚ) / m) > 1 := by
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- **OPEN target.** Twin: the same bound at 8000000. This is an unrefereed public search, unit U-1615
reproduced only its candidate counts 213 and 420, not the search itself. No Lean proof exists. -/
theorem lcm_ge_8000000 : LcmBound 5 8000000 := by
  intro S hS hi hp
  by_contra hcon
  push Not at hcon
  have hpos : ∀ s ∈ S, 0 < s.1 := by
    intro s hs
    obtain ⟨p, -, h5, h⟩ := hp s hs
    omega
  have hL : 0 < S.lcm Prod.fst := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨s, hs, h⟩ := Finset.lcm_eq_zero_iff.1 h0 |> fun h => (Set.mem_image _ _ _).1 h
    exact (hpos s hs).ne' h
  have hT : ∀ m ∈ S.image Prod.fst, m ∣ S.lcm Prod.fst ∧
      (m + 1).Prime ∧ 4 ≤ m := by
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨Finset.dvd_lcm hs, ?_⟩
    obtain ⟨p, hpp, h5, h⟩ := hp s hs
    have e : s.1 + 1 = p := by omega
    refine ⟨by rw [e]; exact hpp, ?_⟩
    omega
  have hsum := one_le_sum_inv hS hpos
  have hsmall : (∑ m ∈ S.image Prod.fst, (1 : ℚ) / m) < 1 := by
    -- BLOCKED 2026-11-25 FREE-nv-mistral task3457 lcm_ge_8000000:
    -- exact missing result: a Lean-checked exhaustive residue assignment certificate for the 420 candidate lcms
    -- in [4000000, 8000000). The reciprocal-sum route is false, as proved above.
    sorry
  have heq : (∑ s ∈ S, (1 : ℚ) / s.1) = ∑ m ∈ S.image Prod.fst, (1 : ℚ) / m := by
    exact (Finset.sum_image (s := S) (g := Prod.fst)
      (f := fun d : ℕ => (1 : ℚ) / d) hi).symm
  rw [heq] at hsum
  exact absurd hsum (not_le.2 hsmall)

end LeanLab.OpenProblems.Novelty1615
