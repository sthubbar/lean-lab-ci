import LeanLab.RamareSaouter2003.Lemma3Zeta

/-!
P0099, display 2 on printed p. 12 and its written proof on pp. 22 and 23.
This is a cited paper statement with explicit asymptotic quantifiers.
No proof is asserted. Claude must review this statement before merge.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Asymptotic290

open Real L3Zeta

/-- CITED. Display 2: at all sufficiently large verified RH heights T0,
some interval parameter Delta grows at least as a positive constant times
T0 divided by the square root of log T0. The interval conclusion is uniform
for every x at least the square of the product T0 log T0. -/
def display2_stmt : Prop :=
  ∃ c T1 : ℝ, 0 < c ∧ 2 ≤ T1 ∧
    ∀ T0 : ℝ, T1 ≤ T0 → RHUpTo T0 → ∃ Δ : ℝ, 1 ≤ Δ ∧
      c * T0 / √(Real.log T0) ≤ Δ ∧
      ∀ x : ℝ, (T0 * Real.log T0) ^ 2 ≤ x →
        ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / Δ) < p ∧ (p : ℝ) ≤ x

end LeanLab.RamareSaouter2003.Asymptotic290

#print axioms LeanLab.RamareSaouter2003.Asymptotic290.display2_stmt
