/-
PP1993 pages 43, 47 and 48, displays 16, 18, 21 and 22.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
These cited analytic inputs remain OPEN. New paper propositions require review.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Density279
import LeanLab.Languasco2004.MajorData413

namespace LeanLab.Languasco2004.Decomp489a
open Finset Real MeasureTheory Decomp279b
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 43: W2 is the character polynomial with its principal term removed. -/
def characterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (Y t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊Y⌋₊,
    ((Λ n : ℂ) * χ n - if χ = 1 then 1 else 0) * phase ((n : ℝ) * t)

/-- Page 47 display 21: the short character sum, clipped at 1 and Y. -/
def shortCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (Y x h : ℝ) : ℂ :=
  ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h),
    ((Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)

/-- Page 47 display 18: all characters of a fixed positive modulus are summed.
This is not a primitive character sum over moduli. -/
def FixedModulusDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q,
    ∀ T σ : ℝ, 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      (∑ χ : DirichletCharacter ℂ q, Density279.zeroCount χ σ T) ≤
        ENNReal.ofReal (C * ((q : ℝ) * T) ^ ((12 / 5 + ε) * (1 - σ)) *
          Real.log ((q : ℝ) * T) ^ (14 : ℕ))

/-- LEAF. Page 47 display 18, cited from Montgomery Theorem 12.1 and Huxley.
The implicit constant depends on positive epsilon only. -/
theorem density_input : FixedModulusDensity := by sorry

/-- Page 47 before display 17: the zero free region including Siegel's input.
The principal character pole is excluded from the zero convention. -/
def CharacterZeroFreeRegion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ _ : NeZero q,
    ∀ χ : DirichletCharacter ℂ q, ∀ s : ℂ,
      (χ ≠ 1 ∨ s ≠ 1) →
      1 - c / max ((q : ℝ) ^ ε) (Real.log (|s.im| + 2) ^ (4 / 5 : ℝ)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0

/-- LEAF. Page 47 before display 17, cited from Prachar Chapter 8 and Siegel.
The constant is allowed to be ineffective. -/
theorem zero_free_input : CharacterZeroFreeRegion := by sorry

/-- Page 47 display 21, first inequality, cited from Gallagher.
The short window has length qQ divided by two. -/
def CharacterGallagher : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ χ : DirichletCharacter ℂ q,
    ∀ Y Q : ℝ, 0 < Y → 0 < Q →
      (∫ t in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
        ‖characterSum χ Y t‖ ^ 2) ≤
      C / ((q : ℝ) * Q) ^ 2 *
        ∫ x in Set.Icc (-((q : ℝ) * Q / 2)) Y,
          ‖shortCharacterSum χ Y x ((q : ℝ) * Q / 2)‖ ^ 2

/-- LEAF. Page 47 display 21, cited from Gallagher 1970.
Only the Fourier to short sum inequality is asserted. -/
theorem gallagher_input : CharacterGallagher := by sorry

/-- Page 48 display 22 as used for the good characters in display 25.
The character must satisfy the zero free rectangle of page 47 display 16.
The constants depend on the fixed positive rectangle parameter B.
F contains precisely the distinct zeros in the displayed strip and height.
The existing multiplicity convention supplies each zero's multiplicity. -/
def CharacterExplicitFormula : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C N₀ : ℝ, 0 < C ∧
    ∀ N Y : ℝ, N₀ ≤ N → 2 ≤ Y → Y ≤ N →
    ∀ q : ℕ, ∀ _ : NeZero q, (q : ℝ) ≤ Y →
    ∀ χ : DirichletCharacter ℂ q,
      (∀ ρ : ℂ, (χ ≠ 1 ∨ ρ ≠ 1) →
        1 - 2 * B * Real.log (Real.log N) / Real.log N ≤ ρ.re →
        ρ.re ≤ 1 → |ρ.im| ≤ Y → DirichletCharacter.LFunction χ ρ ≠ 0) →
    ∀ x : ℝ, 4 ≤ x → x ≤ 2 * Y →
    ∃ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ Y) ∧
      ‖(∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n) -
          (if χ = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ F, (LeanLab.LanguascoPerelli1996.mult χ ρ : ℂ) *
            (x : ℂ) ^ ρ / ρ‖ ≤ C * Real.log N ^ (2 : ℕ)

/-- LEAF. Page 48 display 22, cited from Prachar Chapter 7 Satz 4.4,
restricted to the good characters of display 16 used in display 25.
This asserts no formula for bad characters and no bound for the zero sum. -/
theorem explicit_formula_input : CharacterExplicitFormula := by sorry

#print axioms characterSum
#print axioms shortCharacterSum
#print axioms FixedModulusDensity
#print axioms CharacterZeroFreeRegion
#print axioms CharacterGallagher
#print axioms CharacterExplicitFormula
#print axioms density_input
#print axioms zero_free_input
#print axioms gallagher_input
#print axioms explicit_formula_input
end
end LeanLab.Languasco2004.Decomp489a
