/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The prime modulus consequence of MM14 with primitivity discharged.
CONDITIONAL ON MM14 and the displayed Siegel zero hypothesis.
Source: Matomaki and Merikoski, arXiv 2112.11412v2, printed page 3,
Theorem 1.4. The existing U1451 statement is unchanged.
-/
import LeanLab.Routes.Task59Primitive

namespace LeanLab.Routes.Task59

open LeanLab.Routes.U1451

/-- The prime modulus consequence of MM14 without a separate primitivity input. -/
theorem goldbach_small_of_MM14_prime (hMM : MM14) (C : ℝ) (hC : 1 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (q : ℕ) [Fact q.Prime] [NeZero q]
      (χ : DirichletCharacter ℂ q) (η : ℝ) (h : ℕ),
      q % 4 = 3 → χ.IsQuadratic → χ ≠ 1 → 10 ≤ η →
      DirichletCharacter.LFunction χ ((1 - 1 / (η * Real.log q) : ℝ) : ℂ) = 0 →
      (q : ℝ) ^ 10 ≤ h → q ∣ h →
      |goldbachSum h| ≤ K * errTerm C ε η q h := by
  obtain ⟨K, hK⟩ := goldbach_small_of_MM14 hMM C hC ε hε
  refine ⟨K, ?_⟩
  intro q _ _ χ η h hq4 hχ h1 hη hL hh hqh
  exact hK q χ η h hq4 (primitive_of_prime_ne_one χ h1) hχ h1 hη hL hh hqh

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.goldbach_small_of_MM14_prime
