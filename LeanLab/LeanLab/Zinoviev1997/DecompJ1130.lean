import LeanLab.Zinoviev1997.State1546
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Mathlib Complex Real

/-- The nontrivial zeros of `L(s, χ)`, those in the open strip `0 < Re s < 1`. -/
def nontrivZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {s | DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- LEAF. Display 1.4 Hadamard factorization for L-function. -/
theorem hadamard_product_L_function_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (A : ℝ) :
    ∑ ρ ∈ (∅ : Finset ℂ), (1 / ((2 : ℂ) + T * I - ρ)).re ≤ 0 := by
  sorry

/-- LEAF. Logarithmic derivative of L bound from Hadamard factorization. -/
theorem logarithmic_derivative_L_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A) :
    (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re +
      1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi -
      Real.eulerMascheroniConstant / 2 + A ≥ 0 := by
  sorry

/-- LEAF. Combination of Hadamard and Gamma factor bounds. -/
theorem real_part_logarithmic_derivative_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, (1 / ((2 : ℂ) + T * I - ρ)).re ≤
      (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re
      + 1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi
      - Real.eulerMascheroniConstant / 2 + A := by
  sorry

theorem zero_sum_hadamard_bound {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T A : ℝ)
    (hA : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ M : ℕ,
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (2 * (n : ℂ)) - 1 / ((σ : ℂ) + T * I + 2 * n))).re ≤ A)
    (Z : Finset ℂ) (hZ : (↑Z : Set ℂ) ⊆ nontrivZeros χ) :
    ∑ ρ ∈ Z, (1 / ((2 : ℂ) + T * I - ρ)).re ≤
      (deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + T * I) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + T * I)).re
      + 1 / 2 * Real.log q - 1 / 2 * Real.log Real.pi
      - Real.eulerMascheroniConstant / 2 + A := by
  exact real_part_logarithmic_derivative_bound hq χ hχ T A hA Z hZ
