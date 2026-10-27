/-
P0028, https://arxiv.org/abs/1610.02017, Theorem 4.1, page 7.
The paper assumes positive N. The sealed statement also admits zero.
At zero its sumset hypothesis is impossible, so this extension is harmless.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS
open Finset

/-- Empty sets have every candidate sum popular because the threshold is zero. -/
theorem popular_empty_empty (N : ℕ) (δ : ℝ) :
    popular N δ ∅ ∅ = range (2 * N + 1) := by
  simp [popular, rep]

/-- At N = 0 the sumset hypothesis of Theorem 4.1 cannot hold. -/
theorem thm41_zero_hyp_impossible (ε δ : ℝ) (A B : Finset ℕ)
    (hA : A ⊆ Icc 1 0) (hB : B ⊆ Icc 1 0) :
    ¬ ((popular 0 δ A B).card : ℝ) ≤ 4 * (min A.card B.card : ℕ) - ε * 0 := by
  have hAe : A = ∅ := by simpa using hA
  have hBe : B = ∅ := by simpa using hB
  subst A
  subst B
  simp [popular_empty_empty]

/-- The positive N paper form implies the sealed form. CONDITIONAL ON that paper input. -/
theorem thm41_of_positive
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > (0 : ℝ),
      ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → A ⊆ Icc 1 N → B ⊆ Icc 1 N →
      ((popular N δ A B).card : ℝ) ≤ 4 * (min A.card B.card : ℕ) - ε * N →
      ∃ P : Finset ℕ, IsAPIn N P ∧ δ * N ≤ P.card ∧
        (1 / 2 + ε / 5) * P.card ≤ (A ∩ P).card) : Thm41 := by
  intro ε hε hε1
  obtain ⟨δ, hδ, h⟩ := H ε hε hε1
  refine ⟨δ, hδ, ?_⟩
  intro N A B hA hB hS
  by_cases hN : 0 < N
  · exact h N A B hN hA hB hS
  · have hN0 : N = 0 := by omega
    subst N
    exact (thm41_zero_hyp_impossible ε δ A B hA hB (by simpa only [Nat.cast_zero] using hS)).elim

end LeanLab.Ternary.MMS
