/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Elementary discharge of the primitivity input for prime moduli in U1451.
Source: Matomaki and Merikoski, arXiv 2112.11412v2, printed page 3,
Theorem 1.4. This file proves no assertion about a Siegel zero.
-/
import LeanLab.Routes.U1451MMSiegel

namespace LeanLab.Routes.Task59

/-- A nonprincipal character of prime level has conductor equal to its level. -/
theorem primitive_of_prime_ne_one {q : ℕ} [Fact q.Prime]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.primitive_of_prime_ne_one
