/-
AI wrote this Lean code for CODEX task03.
P0074, page 13, the unit residue masses in the character expansion.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.WeightedCharacters

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The complex mass in one unit residue class of a finite real sequence. -/
noncomputable def unitMass {q : ℕ} (W : Finset ℤ) (ω : ℤ → ℝ) (u : (ZMod q)ˣ) : ℂ :=
  ∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = (u : ZMod q)), (ω m : ℂ)

/-- Grouping a character sum by its unit residue classes loses no character contribution. -/
theorem unitMass_character_sum {q : ℕ} [NeZero q] (W : Finset ℤ) (ω : ℤ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    ∑ u : (ZMod q)ˣ, unitMass W ω u * χ (u : ZMod q) =
      ∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q) := by
  classical
  simp_rw [unitMass, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hu : IsUnit (m : ZMod q)
  · let u : (ZMod q)ˣ := hu.unit
    have huc : (u : ZMod q) = (m : ZMod q) := hu.unit_spec
    have heq : ∀ v : (ZMod q)ˣ, ((m : ZMod q) = (v : ZMod q)) ↔ v = u := by
      intro v
      rw [← huc, Units.val_inj]
      exact eq_comm
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, huc]
  · have heq : ∀ u : (ZMod q)ˣ, (m : ZMod q) ≠ (u : ZMod q) := by
      intro u heq
      exact hu (heq.symm ▸ u.isUnit)
    simp only [heq, ite_false, Finset.sum_const_zero, χ.map_nonunit hu, mul_zero]

/-- The window character condition also holds for its vector of unit residue masses. -/
theorem unitMass_character_bound {q : ℕ} [NeZero q] {W : Finset ℤ} {ω : ℤ → ℝ}
    {M E : ℝ} (h : CharacterEquidist W q ω M E) :
    ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ u : (ZMod q)ˣ, unitMass W ω u * χ (u : ZMod q)) -
        (if χ = 1 then (M : ℂ) else 0)‖ ≤ E := by
  intro χ
  rw [unitMass_character_sum]
  exact h χ

/-- The sharp weighted test estimate for the original finite window masses. -/
theorem unitMass_test_bound {q : ℕ} [NeZero q] {W : Finset ℤ} {ω : ℤ → ℝ}
    {M E : ℝ} (hE : 0 ≤ E) (h : CharacterEquidist W q ω M E)
    (f : (ZMod q)ˣ → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖(∑ u : (ZMod q)ˣ, unitMass W ω u * f u) -
      (M : ℂ) / q.totient * ∑ u : (ZMod q)ˣ, f u‖ ≤ Real.sqrt q.totient * E :=
  unit_test_bound (unitMass W ω) f M hE (unitMass_character_bound h) hf

#print axioms unitMass_character_sum
#print axioms unitMass_character_bound
#print axioms unitMass_test_bound
end LeanLab.Grimmelt2019.MainTerm
