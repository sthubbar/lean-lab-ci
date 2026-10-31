/-
Concrete instances for the task96 twins from P0089 pages 223 to 227.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Count96

namespace LeanLab.Languasco2004

attribute [local instance] Classical.propDecidable

/-- Concrete instances for the page 223 and page 227 exception predicates,
and the finite positive set used by the counting equivalences. -/
theorem task96_vacuity_instances :
    EXH 4 0 = 0 ∧ EX 4 = 0 ∧ EkXH 2 3 0 = 0 ∧
      {n : ℕ | 1 ≤ n ∧ n = 3}.Finite := by
  have hfour : IsGoldbachSum 4 := ⟨2, 2, by decide, by decide, rfl⟩
  have hthree : IsHL 2 3 := ⟨2, 1, by decide, by decide, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (EXH_eq_zero_iff 4 0).mpr
    intro n hn hn' _ _
    have hn4 : (n : ℝ) = 4 := by linarith
    have : n = 4 := by exact_mod_cast hn4
    simpa [this] using hfour
  · apply (EXH_eq_zero_iff 1 (4 - 1)).mpr
    intro n _ hn he h2
    have hn4 : n ≤ 4 := by exact_mod_cast (show (n : ℝ) ≤ 4 by linarith)
    have hmod := Nat.even_iff.mp he
    have : n = 4 := by omega
    simpa [this] using hfour
  · unfold EkXH
    rw [Finset.card_filter_eq_zero_iff]
    intro n _ hn
    have hn3 : (n : ℝ) = 3 := by have := hn.1; have := hn.2.1; linarith
    have : n = 3 := by exact_mod_cast hn3
    exact hn.2.2.1 (by simpa [this] using hthree)
  · exact (Set.finite_singleton (3 : ℕ)).subset (fun n hn => hn.2)

#print axioms task96_vacuity_instances

end LeanLab.Languasco2004
