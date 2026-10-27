/-
AI wrote this Lean code for CODEX task121.
P0037 Theorem 1, printed page 206, computational argument on pages 209 to 211.
P0005 is a different paper and has no written proof of this theorem.
This is the requested fallback decomposition of the main cited theorem.
The three computational leaves are unproved cited inputs.
The assembly is CONDITIONAL ON those leaves. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Theorem1

namespace LeanLab.DtRS1998.Decomp121

open LeanLab Theorem1

/-- LEAF. P0037 page 205 and Section 4 page 208. The inherited verification
through 4 times 10^11 is cited from Sinisalo 1993, reference 16 in P0037.
This external published computation is not proved here. -/
theorem inherited_range : EvenGoldbachUpTo (4 * 10 ^ 11) := by
  sorry

/-- LEAF. P0037 Section 4.1, printed page 210. The four intervals reported
for the Cray C916. This published computation is not proved here. -/
theorem cray_ranges :
    ∀ n : ℕ, Even n →
      ((4 * 10 ^ 11 ≤ n ∧ n ≤ 10 ^ 13) ∨
       (2 * 10 ^ 13 ≤ n ∧ n ≤ 4 * 10 ^ 13) ∨
       (6 * 10 ^ 13 ≤ n ∧ n ≤ 8 * 10 ^ 13) ∨
       (9 * 10 ^ 13 ≤ n ∧ n ≤ 10 ^ 14)) → IsGoldbachSum n := by
  sorry

/-- LEAF. P0037 Section 4.2, printed page 211. The three intervals reported
for the SGI compute server. This published computation is not proved here. -/
theorem sgi_ranges :
    ∀ n : ℕ, Even n →
      ((10 ^ 13 ≤ n ∧ n ≤ 2 * 10 ^ 13) ∨
       (4 * 10 ^ 13 ≤ n ∧ n ≤ 6 * 10 ^ 13) ∨
       (8 * 10 ^ 13 ≤ n ∧ n ≤ 9 * 10 ^ 13)) → IsGoldbachSum n := by
  sorry

/-- LEAF. P0037 Sections 4.1 and 4.2, printed pages 210 and 211.
The inherited interval and the seven reported intervals cover the target range. -/
theorem ranges_cover {n : ℕ} (hn : n ≤ 10 ^ 14) :
    n ≤ 4 * 10 ^ 11 ∨
    ((4 * 10 ^ 11 ≤ n ∧ n ≤ 10 ^ 13) ∨
     (2 * 10 ^ 13 ≤ n ∧ n ≤ 4 * 10 ^ 13) ∨
     (6 * 10 ^ 13 ≤ n ∧ n ≤ 8 * 10 ^ 13) ∨
     (9 * 10 ^ 13 ≤ n ∧ n ≤ 10 ^ 14)) ∨
    ((10 ^ 13 ≤ n ∧ n ≤ 2 * 10 ^ 13) ∨
     (4 * 10 ^ 13 ≤ n ∧ n ≤ 6 * 10 ^ 13) ∨
     (8 * 10 ^ 13 ≤ n ∧ n ≤ 9 * 10 ^ 13)) := by
  have h : n ∈ Set.Icc (0 : ℕ) (10 ^ 14) := ⟨Nat.zero_le n, hn⟩
  have hsplit : ∀ a b c : ℕ, Set.Icc a c ⊆ Set.Icc a b ∪ Set.Icc b c :=
    fun _ _ _ => Set.Icc_subset_Icc_union_Icc
  rcases hsplit 0 (4 * 10 ^ 11) (10 ^ 14) h with h | h
  · exact Or.inl h.2
  rcases hsplit (4 * 10 ^ 11) (10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inl (Or.inl h))
  rcases hsplit (10 ^ 13) (2 * 10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  rcases hsplit (2 * 10 ^ 13) (4 * 10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
  rcases hsplit (4 * 10 ^ 13) (6 * 10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rcases hsplit (6 * 10 ^ 13) (8 * 10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))
  rcases hsplit (8 * 10 ^ 13) (9 * 10 ^ 13) (10 ^ 14) h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h))))

/-- CONDITIONAL ON the supplied computational ranges. P0037 pages 206 and 210 to 211.
This isolates the assembly and has no dependency on the unproved leaves. -/
theorem theorem1_of_ranges
    (hbase : EvenGoldbachUpTo (4 * 10 ^ 11))
    (hcray : ∀ n : ℕ, Even n →
      ((4 * 10 ^ 11 ≤ n ∧ n ≤ 10 ^ 13) ∨
       (2 * 10 ^ 13 ≤ n ∧ n ≤ 4 * 10 ^ 13) ∨
       (6 * 10 ^ 13 ≤ n ∧ n ≤ 8 * 10 ^ 13) ∨
       (9 * 10 ^ 13 ≤ n ∧ n ≤ 10 ^ 14)) → IsGoldbachSum n)
    (hsgi : ∀ n : ℕ, Even n →
      ((10 ^ 13 ≤ n ∧ n ≤ 2 * 10 ^ 13) ∨
       (4 * 10 ^ 13 ≤ n ∧ n ≤ 6 * 10 ^ 13) ∨
       (8 * 10 ^ 13 ≤ n ∧ n ≤ 9 * 10 ^ 13)) → IsGoldbachSum n) :
    G2AtLeast (10 ^ 14) := by
  intro n he h4 hn
  rcases ranges_cover hn.le with hlow | hmiddle | hhigh
  · exact hbase n he h4 hlow
  · exact hcray n he hmiddle
  · exact hsgi n he hhigh

/-- CONDITIONAL ON the three cited computational ranges.
P0037 Theorem 1, printed page 206, with exactly the lab's faithful target. -/
theorem theorem1 : G2AtLeast (10 ^ 14) :=
  theorem1_of_ranges inherited_range cray_ranges sgi_ranges

#print axioms inherited_range
#print axioms cray_ranges
#print axioms sgi_ranges
#print axioms ranges_cover
#print axioms theorem1_of_ranges
#print axioms theorem1

end LeanLab.DtRS1998.Decomp121
