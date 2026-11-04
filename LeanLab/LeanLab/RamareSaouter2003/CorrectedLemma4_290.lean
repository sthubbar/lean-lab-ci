import LeanLab.RamareSaouter2003.Lemma1Zeta

/-!
P0099, Lemma 4, printed pp. 15 and 16, with the correction of Ramare 2023,
Lemma 1.1. This records the full general weight statement beside the
specialized OPEN leaves of Decomp290c. It is a cited Prop, not a proof.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.CorrectedLemma4_290

open Real Chebyshev L3Zeta

/-- CITED. The corrected Lemma 4 for a continuously differentiable real weight.
P0099 pp. 15 and 16. Ramare 2023, Lemma 1.1, changes the constant to minus
log 2pi. The zero family includes multiplicity. -/
def lemma4_corrected_stmt : Prop :=
  ∀ a b : ℝ, 2 ≤ a → a ≤ b → ∀ g : ℝ → ℝ, ContDiffOn ℝ 1 g (Set.Icc a b) →
    (∫ t in a..b, ψ t * g t) = (∫ t in a..b, t * g t) -
      (∑' i : ZI, ∫ t in a..b, (t : ℂ) ^ (i.1 : ℂ) / (i.1 : ℂ) * (g t : ℂ)).re -
      ∫ t in a..b, (Real.log (2 * π) + (1 / 2) * Real.log (1 - t ^ (-2 : ℤ))) * g t

/-- The corrected constant cancels in the difference used before display 13
on P0099 p. 19. This follows directly from Mathlib cancellation and mul_sub. -/
theorem corrected_constant_difference (Z u : ℝ) :
    (Real.log (2 * π) + (1 / 2) * Real.log (1 - 1 / (Real.exp u * Z) ^ 2)) -
      (Real.log (2 * π) + (1 / 2) * Real.log (1 - 1 / Z ^ 2)) =
      (1 / 2) * (Real.log (1 - 1 / (Real.exp u * Z) ^ 2) -
        Real.log (1 - 1 / Z ^ 2)) := by
  rw [add_sub_add_left_eq_sub, mul_sub]

/-- The sign correction to log 2pi in Lemma 4 leaves its pointwise
psi difference contribution unchanged. Compare P0099 p. 15 with Ramare
2023 Lemma 1.1, before taking the difference used on P0099 p. 19. -/
theorem erratum_difference_unchanged (A B : ℝ) :
    (-Real.log (2 * π) - (1 / 2) * Real.log (1 - A ^ (-2 : ℤ))) -
      (-Real.log (2 * π) - (1 / 2) * Real.log (1 - B ^ (-2 : ℤ))) =
      (Real.log (2 * π) - (1 / 2) * Real.log (1 - A ^ (-2 : ℤ))) -
      (Real.log (2 * π) - (1 / 2) * Real.log (1 - B ^ (-2 : ℤ))) := by
  simp only [sub_sub_sub_cancel_left]

end LeanLab.RamareSaouter2003.CorrectedLemma4_290

#print axioms LeanLab.RamareSaouter2003.CorrectedLemma4_290.lemma4_corrected_stmt
#print axioms LeanLab.RamareSaouter2003.CorrectedLemma4_290.corrected_constant_difference

#print axioms LeanLab.RamareSaouter2003.CorrectedLemma4_290.erratum_difference_unchanged
