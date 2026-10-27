import LeanLab.Ricci1937.CIdentity
import LeanLab.Ricci1937.CCounts

/-!
Ricci 1937, page 83: the identity polynomial case of C2 at s = 3.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The s = 3 identity count agrees exactly with the C1 identity count. -/
lemma c2ValueCount_identity_three (ξ : ℕ) :
    c2ValueCount (Polynomial.X : Polynomial ℤ) 3 ξ = c1IdentityCount ξ := by
  have hP : CHyp (Polynomial.X : Polynomial ℤ) :=
    ⟨by simp, Polynomial.monic_X.isPrimitive, Polynomial.irreducible_X, by simp⟩
  have h := c1_count_eq_c2_three_mul (Polynomial.X : Polynomial ℤ) hP ξ
  simpa [c2ValueCount, c1IdentityCount,
    Fval_of_linear Polynomial.monic_X.isPrimitive (by simp)] using h.symm

/-- The full two sided C2 count for F = X and s = 3, with no cited input. -/
theorem theoremC2_identity_three :
    ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      a₁ * ξ / Real.log ξ < c2ValueCount (Polynomial.X : Polynomial ℤ) 3 ξ ∧
      (c2ValueCount (Polynomial.X : Polynomial ℤ) 3 ξ : ℝ) < a₂ * ξ / Real.log ξ := by
  simpa only [c2ValueCount_identity_three] using c1Identity_estimate

end
end LeanLab.Ricci1937
