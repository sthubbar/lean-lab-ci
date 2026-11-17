import LeanLab.RamareSaouter2003.Lemma1Zeta

/-!
P0099 pp. 19 and 20, displays 13 through 15.
The existing zeroTerm definition is moved here with identical text.
This separates the zero term from the explicit formula proofs.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp290c

open Real Chebyshev Smooth Thm4Assembly L3Zeta

/-- The zero term in display 13, printed p. 19, after zero_term_factor. -/
noncomputable def zeroTerm (m : ℕ) (X u : ℝ) (i : ZI) : ℂ :=
  (Complex.exp (u * (i.1 : ℂ)) - 1) / (i.1 : ℂ) * (X : ℂ) ^ (i.1 : ℂ) *
    ∫ t in (0 : ℝ)..1,
      (((1 + (m * u) * t : ℝ) : ℂ) ^ (i.1 : ℂ)) * (fm m t : ℂ)

end LeanLab.RamareSaouter2003.Decomp290c

#print axioms LeanLab.RamareSaouter2003.Decomp290c.zeroTerm
