import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.TheoremAU1357

/-!
P0054 author copy page 8 displays 2.20 and 2.21.
These are finite data templates for the displayed formulas.
The analytic choice of P and the exceptional zero data remain cited inputs.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.DiscreteFormulaTask08

open Finset WeightedKernelsTask08 TheoremAU1357

/-- The finite main sum with the exact discrete kernel. -/
noncomputable def discreteMain {K : ℕ} (D : ZeroData K) (X1 X : ℝ)
    (m : ℕ) (difference : Bool) : ℂ :=
  ∑ i, ∑ j, ((D.A i : ℂ) * D.A j) * D.Sg i j m *
    weightedKernel X1 X (D.ρ i) (D.ρ j) m difference

/-- The displayed error bound with explicit constants and supplied finite data.
This does not assert that actual major arc integrals satisfy the bound. -/
def FormulaBound {K : ℕ} (D : ZeroData K) (R1 : ℕ → ℂ)
    (X1 X ε c H Cexp Cpower : ℝ) (difference : Bool) : Prop :=
  ∀ m : ℕ, (m : ℝ) ≤ X →
    ‖R1 m - discreteMain D X1 X m difference‖ ≤
      Cexp * Sing m * X * Real.exp (-(c * H)) + Cpower * X ^ (1 - ε)

/-- A single pole with arbitrary supplied singular series. -/
noncomputable def poleData (S : ℕ → ℂ) : ZeroData 1 where
  A := fun _ => 1
  ρ := fun _ => 1
  r := fun _ => 1
  Sg := fun _ _ => S

/-- At the single pole the main sum is the singular series times the pair count. -/
theorem discreteMain_pole (S : ℕ → ℂ) (X1 X : ℝ) (m : ℕ) (difference : Bool) :
    discreteMain (poleData S) X1 X m difference =
      S m * ((kernelPairs X1 X m difference).card : ℂ) := by
  simp [discreteMain, poleData, weightedKernel_poles]

/-- A nonzero finite pole model has zero error in either formula template. -/
theorem formulaBound_pole (S : ℕ → ℂ) (X1 X ε c H : ℝ) (difference : Bool) :
    FormulaBound (poleData S)
      (fun m => S m * ((kernelPairs X1 X m difference).card : ℂ))
      X1 X ε c H 0 0 difference := by
  intro m _
  simp [discreteMain_pole]

/-- The triangle bound for the finite main sum. -/
theorem norm_discreteMain_le {K : ℕ} (D : ZeroData K) (X1 : ℝ) {X : ℝ}
    (hX : 0 ≤ X) (hρ : ∀ i, (D.ρ i).re ≤ 1) (m : ℕ) (difference : Bool) :
    ‖discreteMain D X1 X m difference‖ ≤
      ∑ i, ∑ j, (|D.A i| * |D.A j|) * ‖D.Sg i j m‖ * X := by
  unfold discreteMain
  calc _ ≤ ∑ i, ‖∑ j, ((D.A i : ℂ) * D.A j) * D.Sg i j m *
          weightedKernel X1 X (D.ρ i) (D.ρ j) m difference‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖((D.A i : ℂ) * D.A j) * D.Sg i j m *
          weightedKernel X1 X (D.ρ i) (D.ρ j) m difference‖ :=
      sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_weightedKernel_le_X X1 hX (hρ i) (hρ j) m difference) (by positivity)

/-- Signs bounded by one and singular series bounded by B give K squared B X. -/
theorem norm_discreteMain_le_card_sq {K : ℕ} (D : ZeroData K) (X1 : ℝ) {X B : ℝ}
    (hX : 0 ≤ X) (hρ : ∀ i, (D.ρ i).re ≤ 1) (hA : ∀ i, |D.A i| ≤ 1)
    (m : ℕ) (hS : ∀ i j, ‖D.Sg i j m‖ ≤ B) (difference : Bool) :
    ‖discreteMain D X1 X m difference‖ ≤ (K : ℝ) ^ 2 * B * X := by
  calc _ ≤ ∑ i, ∑ j, (|D.A i| * |D.A j|) * ‖D.Sg i j m‖ * X :=
          norm_discreteMain_le D X1 hX hρ m difference
    _ ≤ ∑ _i : Fin K, ∑ _j : Fin K, B * X := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ hX
      have hAA : |D.A i| * |D.A j| ≤ 1 := by
        simpa using mul_le_mul (hA i) (hA j) (abs_nonneg _) zero_le_one
      simpa using mul_le_mul hAA (hS i j) (norm_nonneg _) zero_le_one
    _ = _ := by simp; ring

end LeanLab.Pintz2021.DiscreteFormulaTask08

#print axioms LeanLab.Pintz2021.DiscreteFormulaTask08.discreteMain_pole

#print axioms LeanLab.Pintz2021.DiscreteFormulaTask08.formulaBound_pole

#print axioms LeanLab.Pintz2021.DiscreteFormulaTask08.norm_discreteMain_le

#print axioms LeanLab.Pintz2021.DiscreteFormulaTask08.norm_discreteMain_le_card_sq
