import LeanLab.OpenProblems.Erdos273

namespace LeanLab.OpenProblems.Erdos273

inductive CoverTree (M : ℕ)
| leaf (a : ℤ) (d : ℕ) (h_d_div_M : (d : ℤ) ∣ (M : ℤ)) : CoverTree M
| split (p : ℕ) (h_p_div_M : (p : ℤ) ∣ (M : ℤ)) (branches : Fin p → CoverTree M) : CoverTree M

/-- Extract the list of congruences from the tree. -/
def CoverTree.toList {M : ℕ} : CoverTree M → List (ℕ × ℤ)
| leaf a d _ => [(d, a)]
| split _ _ branches => List.flatten (List.ofFn (fun i => (branches i).toList))

/-- Extract the property that a tree is valid. -/
def CoverTree.Valid {M : ℕ} : CoverTree M → Prop
| leaf _ d _ => d = 1
| split p _ branches => 0 < p ∧ ∀ i, (branches i).Valid

/-- LEAF A leaf node covers the class a mod d. -/
theorem covers_of_tree_leaf {M : ℕ} (a : ℤ) (d : ℕ) (h_d_div_M : (d : ℤ) ∣ (M : ℤ)) :
  ∀ x : ℤ, x % (d : ℤ) = a % (d : ℤ) → ∃ s ∈ (CoverTree.leaf (M:=M) a d h_d_div_M).toList, (s.1 : ℤ) ∣ (x - s.2) := by
  intro x hx
  use (d, a)
  simp only [CoverTree.toList, List.mem_singleton, true_and]
  have h_modeq : x ≡ a [ZMOD (d : ℤ)] := hx
  exact Int.ModEq.dvd h_modeq.symm

/-- LEAF A split node covers all classes modulo p. -/
theorem covers_of_tree_split {M : ℕ} (p : ℕ) (h_p_pos : 0 < p) (h_p_div_M : (p : ℤ) ∣ (M : ℤ))
  (branches : Fin p → CoverTree M)
  (h_branches : ∀ (i : Fin p) (x : ℤ), x % (p : ℤ) = (i.1 : ℤ) → ∃ s ∈ (branches i).toList, (s.1 : ℤ) ∣ (x - s.2)) :
  ∀ x : ℤ, ∃ s ∈ (CoverTree.split (M:=M) p h_p_div_M branches).toList, (s.1 : ℤ) ∣ (x - s.2) := by
  intro x
  have hp_pos : 0 < (p : ℤ) := by exact_mod_cast h_p_pos
  have h_mod : 0 ≤ x % (p : ℤ) ∧ x % (p : ℤ) < (p : ℤ) := ⟨Int.emod_nonneg x hp_pos.ne', Int.emod_lt_of_pos x hp_pos⟩
  set i : Fin p := ⟨(x % (p : ℤ)).toNat, by omega⟩
  obtain ⟨s, hs, hdiv⟩ := h_branches i x (by simp [i, Int.toNat_of_nonneg h_mod.1])
  use s
  constructor
  · simp only [CoverTree.toList, List.mem_flatten, List.mem_ofFn]
    exact ⟨(branches i).toList, ⟨i, rfl⟩, hs⟩
  · exact hdiv

/-- LEAF soundness of the tree certificate. -/
theorem covers_of_tree_sound {M : ℕ} (t : CoverTree M) (ht : t.Valid) :
  ∀ x : ℤ, ∃ s ∈ t.toList, (s.1 : ℤ) ∣ (x - s.2) := by
  intro x
  induction t generalizing x with
  | leaf a d h_d_div_M =>
    have hd1 : d = 1 := ht
    use (d, a)
    simp only [CoverTree.toList, List.mem_singleton, true_and]
    subst hd1
    exact one_dvd (x - a)
  | split p h_p_div_M branches ih =>
    have h_p_pos : 0 < p := ht.1
    have h_branches : ∀ i, (branches i).Valid := ht.2
    apply covers_of_tree_split p h_p_pos h_p_div_M branches
    intro i y _
    exact ih i (h_branches i) y

/-- The certificate shape for a tree. -/
theorem covers_of_tree_aux {M : ℕ} (t : CoverTree M)
  (ht: ∀ x : ℤ, ∃ s ∈ t.toList, (s.1 : ℤ) ∣ (x - s.2)) :
  Covers t.toList.toFinset := by
  intro x
  obtain ⟨s, hs, h_div⟩ := ht x
  exact ⟨s, List.mem_toFinset.mpr hs, h_div⟩

/-- The certificate shape for a tree. -/
theorem covers_of_tree {M : ℕ} (t : CoverTree M) (ht_valid : t.Valid) :
  Covers t.toList.toFinset := covers_of_tree_aux t (covers_of_tree_sound t ht_valid)

end LeanLab.OpenProblems.Erdos273
