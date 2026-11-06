import LeanLab.LPZ2007.ZeroFamily373

/-!
P0045 pages 4 and 5, display 8 and the indexed family in Lemma 4.1.
The paper counts zeros with multiplicity.
This audit concerns only the sealed lab interface, which records membership.
Membership alone gives no upper bound on the length of an indexed family.
No error in the paper is asserted.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.FamilyAudit407

/-- P0045 page 4, display 8, a genuine nonempty exceptional box.
The principal character modulo one has its trivial zero at minus two.
This is a fixed small scale instance, not an asymptotic density assertion. -/
theorem nonempty_zero_box : (EZero (Real.exp 2) 6 1 2).Nonempty := by
  refine ⟨⟨1, (1 : DirichletCharacter ℂ 1), (-2 : ℂ)⟩, ?_⟩
  refine ⟨by norm_num, by norm_num, DirichletCharacter.isPrimitive_one_level_one,
    RealZeroProof.real_zero_instance.2, ?_, ?_⟩
  · norm_num [Real.log_exp]
  · norm_num

/-- P0045 page 5, the membership clause in the lab Lemma41 interface.
An indexed family of actual zeros can have arbitrarily many repeated entries.
Its index length cannot be bounded from that membership clause alone. -/
theorem membership_allows_unbounded_index (K : ℕ) :
    ∃ f : Fin (K + 1) → (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ i, f i ∈ EZero (Real.exp 2) 6 1 2) ∧ K < Fintype.card (Fin (K + 1)) := by
  obtain ⟨z, hz⟩ := nonempty_zero_box
  exact ⟨fun _ => z, fun _ => hz, by simp⟩

end LeanLab.LPZ2007.FamilyAudit407

#print axioms LeanLab.LPZ2007.FamilyAudit407.nonempty_zero_box
#print axioms LeanLab.LPZ2007.FamilyAudit407.membership_allows_unbounded_index
