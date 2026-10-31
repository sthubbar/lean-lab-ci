/-
AI wrote this Lean code for CODEX task70.
An array of pair sums speeds up the exact S-algorithm from Section 2, page 427.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-- Accumulate the largest admissible candidate. Zero denotes no positive candidate. -/
def bestAux (isA : ℕ → Bool) (m : ℕ) : List ℕ → ℕ → ℕ
  | [], a => a
  | b :: bs, a =>
    if a < m - b ∧ b ≤ m ∧ isA (m - b) = true then
      bestAux isA m bs (m - b)
    else bestAux isA m bs a

theorem bestAux_spec (isA : ℕ → Bool) (m : ℕ) (bs : List ℕ) (a : ℕ) :
    bestAux isA m bs a = (cands isA bs m).foldl max a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [bestAux, cands, List.filter_cons, List.map_cons, List.map_nil,
      Bool.and_eq_true, decide_eq_true_eq]
    by_cases h : b ≤ m ∧ isA (m - b) = true
    · simp only [h, ↓reduceIte, List.foldl_cons]
      by_cases ha : a < m - b
      · simp [ha, h, ih, max_eq_right (Nat.le_of_lt ha), cands]
      · simp [ha, h, ih, max_eq_left (Nat.le_of_not_gt ha), cands]
    · have hn : ¬ (a < m - b ∧ b ≤ m ∧ isA (m - b) = true) := by tauto
      simp [h, hn, ih, cands]

/-- Mark all new pair sums with the added element. -/
def markSums : List ℕ → Array Bool → ℕ → Array Bool
  | [], arr, _ => arr
  | b :: bs, arr, a => markSums bs (arr.setIfInBounds (a + b) true) a

@[simp] theorem markSums_size (bs : List ℕ) (arr : Array Bool) (a : ℕ) :
    (markSums bs arr a).size = arr.size := by
  induction bs generalizing arr with
  | nil => rfl
  | cons b bs ih => simp [markSums, ih]

theorem markSums_read (bs : List ℕ) (arr : Array Bool) (a m : ℕ) (hm : m < arr.size) :
    (markSums bs arr a)[m]?.getD false = true ↔
      arr[m]?.getD false = true ∨ ∃ b ∈ bs, a + b = m := by
  induction bs generalizing arr with
  | nil => simp [markSums]
  | cons b bs ih =>
    rw [markSums, ih _ (by simpa using hm)]
    by_cases h : a + b = m
    · subst m
      simp [hm]
    · simp [Array.getElem?_setIfInBounds, h, List.mem_cons, or_assoc]

/-- A sum array faithfully represents the current basis within its bounds. -/
def SumInvariant (bs : List ℕ) (arr : Array Bool) : Prop :=
  ∀ m < arr.size, arr[m]?.getD false = true ↔ covers bs m = true

/-- Add the new diagonal sum and the sums with previous elements. -/
def addSums (bs : List ℕ) (arr : Array Bool) (a : ℕ) : Array Bool :=
  markSums bs (arr.setIfInBounds (a + a) true) a

@[simp] theorem addSums_size (bs : List ℕ) (arr : Array Bool) (a : ℕ) :
    (addSums bs arr a).size = arr.size := by simp [addSums]

theorem covers_add (bs : List ℕ) (a m : ℕ) :
    covers (bs ++ [a]) m = true ↔ covers bs m = true ∨ a + a = m ∨
      ∃ b ∈ bs, a + b = m := by
  simp only [covers_iff, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · exact Or.inl ⟨x, hx, y, hy, hxy⟩
    · exact Or.inr (Or.inr ⟨x, hx, by omega⟩)
    · exact Or.inr (Or.inr ⟨y, hy, hxy⟩)
    · exact Or.inr (Or.inl hxy)
  · rintro (⟨x, hx, y, hy, hxy⟩ | h | ⟨b, hb, h⟩)
    · exact ⟨x, Or.inl hx, y, Or.inl hy, hxy⟩
    · exact ⟨a, Or.inr rfl, a, Or.inr rfl, h⟩
    · exact ⟨a, Or.inr rfl, b, Or.inl hb, h⟩

theorem addSums_invariant (bs : List ℕ) (arr : Array Bool) (a : ℕ)
    (h : SumInvariant bs arr) : SumInvariant (bs ++ [a]) (addSums bs arr a) := by
  intro m hm
  have hm' : m < arr.size := by simpa using hm
  rw [addSums, markSums_read _ _ _ _ (by simpa using hm'), covers_add]
  by_cases he : a + a = m
  · subst m
    simp [hm']
  · simp [Array.getElem?_setIfInBounds, he, h m hm', or_assoc]

/-- The same optional maximum as `cands`, with redundant primality tests skipped. -/
def fastCand (isA : ℕ → Bool) (bs : List ℕ) (m : ℕ) : Option ℕ :=
  let a := bestAux isA m bs 0
  if a = 0 then none else some a

theorem fastCand_eq (isA : ℕ → Bool) (bs : List ℕ) (m : ℕ)
    (h0 : isA 0 = false) : fastCand isA bs m = (cands isA bs m).max? := by
  have h := bestAux_spec isA m bs 0
  rw [List.foldl_max] at h
  simp only [Nat.zero_max] at h
  unfold fastCand
  rw [h]
  cases he : (cands isA bs m).max? with
  | none => simp
  | some a =>
    have ha : a ≠ 0 := by
      intro hz
      have hp := (mem_cands (List.max?_mem he)).1
      rw [hz, h0] at hp
      contradiction
    simp [ha]

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.bestAux_spec
#print axioms LeanLab.SteinStein1965.markSums_size
#print axioms LeanLab.SteinStein1965.markSums_read
#print axioms LeanLab.SteinStein1965.addSums_size
#print axioms LeanLab.SteinStein1965.covers_add
#print axioms LeanLab.SteinStein1965.addSums_invariant
#print axioms LeanLab.SteinStein1965.fastCand_eq
