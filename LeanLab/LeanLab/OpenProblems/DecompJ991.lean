import LeanLab.OpenProblems.Erdos273

namespace LeanLab.OpenProblems.Erdos273

/-- LEAF 1: Tree definition for the certificate. -/
inductive CoverTree
| leaf (s : ℕ × ℤ)
| split (p : ℕ) (branches : List CoverTree)

/-- LEAF 2: Definition of what it means for a tree to cover an integer. -/
def CoversTree (t : CoverTree) (x : ℤ) : Prop := sorry

/-- LEAF 3: The soundness of the tree covering implies the list covering. -/
theorem covers_of_tree (t : CoverTree) : (∀ x : ℤ, CoversTree t x) → ∃ L : List (ℕ × ℤ), Covers L.toFinset := sorry

/-- Assembly theorem for Erdos273Statement. -/
theorem Erdos273_assembly (t : CoverTree) (_h : ∀ x : ℤ, CoversTree t x) (hinj : ∃ L : List (ℕ × ℤ), Covers L.toFinset ∧ (L.map Prod.fst).Nodup ∧ ∀ s ∈ L, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) : Erdos273Statement := by
  obtain ⟨L, hc, hinj, hp⟩ := hinj
  refine ⟨L.toFinset, hc, ?_, ?_⟩
  · intro a ha b hb hab
    exact List.inj_on_of_nodup_map hinj (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  · exact fun s hs => hp s (List.mem_toFinset.mp hs)

end LeanLab.OpenProblems.Erdos273
