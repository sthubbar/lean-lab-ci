/-
AI wrote this Lean code for CODEX task70.
The empirical maximum claims in the note on pages 433 and 434 are stated, not proved.
Arithmetic counterexamples explain why those bounds alone do not imply the whole square window.
-/
import LeanLab.SteinStein1965.NoteAdded

namespace LeanLab.SteinStein1965

/-- The cited maximum assertion for the ordinary interval, page 433. -/
def MaxLeastPrimeClaim : Prop :=
  ∀ N, N % 2 = 0 → 63276 ≤ N → N ≤ 10 ^ 8 →
    ∃ q, IsLeastGoldbachPrime N q ∧ q ≤ 1093

/-- The cited maximum assertion for the modified interval, page 434. -/
def MaxLeastP1Claim : Prop :=
  ∀ N, N % 4 = 2 → 1457284 ≤ N → N < 10 ^ 8 →
    ∃ q, IsLeastP1Pair N q ∧ q ≤ 2953

theorem max_bound_not_square_at_lower :
    ∃ N q : ℕ, N % 2 = 0 ∧ 63276 ≤ N ∧ N ≤ 10 ^ 8 ∧
      q ≤ 1093 ∧ ¬ q * q < N := by
  exact ⟨63276, 1093, by decide, by decide, by decide, by decide, by decide⟩

theorem max_bound_not_square_at_lowerP1 :
    ∃ N q : ℕ, N % 4 = 2 ∧ 1457284 ≤ N ∧ N < 10 ^ 8 ∧
      q ≤ 2953 ∧ ¬ q * q < N := by
  exact ⟨1457286, 2953, by decide, by decide, by decide, by decide, by decide⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.max_bound_not_square_at_lower
#print axioms LeanLab.SteinStein1965.max_bound_not_square_at_lowerP1
