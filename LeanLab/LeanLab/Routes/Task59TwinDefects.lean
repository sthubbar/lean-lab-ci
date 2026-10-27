/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Convergence of the defects in the twin constant used by U1451.
Source context: Matomaki and Merikoski, printed page 1, singular series display.
-/
import LeanLab.Routes.U1451MMSiegel

namespace LeanLab.Routes.Task59

/-- The twin constant defects form a convergent series over odd primes. -/
theorem summable_twin_defects :
    Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hi : Function.Injective (fun p : {p : ℕ // p.Prime ∧ 2 < p} => p.1 - 1) := by
    intro p q h
    apply Subtype.ext
    have hp := p.property.2
    have hq := q.property.2
    dsimp at h
    omega
  apply (hs.comp_injective hi).congr
  intro p
  change (1 : ℝ) / (((p.1 - 1 : ℕ) : ℝ) ^ 2) = 1 / ((p.1 : ℝ) - 1) ^ 2
  rw [Nat.cast_sub (by have := p.property.2; omega), Nat.cast_one]

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.summable_twin_defects
