import Mathlib
import LeanLab.Ramare1995.DecompJ1066

/-!
# Flag 1729: Gemini flag on `DecompJ1066.proposition1_leaf`

AI wrote the Lean code. Goldbach is open.

Part 1. Named hypothesis `Proposition1Flag1729` is the exact sealed statement of
`proposition1_leaf`, with a match theorem.

Part 2. Verdict: the flag is NOT confirmed. No negation is proved. The sealed
normalization divides by S2 of N equal to 2 C2 times the odd local factor, which is
the classical singular series. Heuristically paper_R X is about one half of
X squared over log X, above 0.478, so the leaf is expected true and the
factor 2 is correct. Part 3 records that the factor 2 only weakens the claim:
without it the same lower bound would follow from the sealed one.
-/

open Finset Real
open scoped Classical

namespace LeanLab.Ramare1995.Flag1729
open LeanLab.Ramare1995.Decomp1526c LeanLab.Ramare1995.Decomp1526b

/-- Twin: for every real X at least e^67, 0.478 X^2 / log X is at most the
normalized sum R of X from equation 2.14, Ramaré 1995 Proposition 1 p. 653. -/
def Proposition1Flag1729 : Prop :=
  ∀ X : ℝ, exp 67 ≤ X → 0.478 * X ^ 2 / Real.log X ≤ paper_R X

/-- The named hypothesis is literally the sealed Prop `proposition1`. -/
theorem proposition1Flag1729_iff : Proposition1Flag1729 ↔ proposition1 := Iff.rfl

/-- The sum without the factor 2 in the singular series, the reading the flag
suggests as a possible mistranscription. -/
noncomputable def paper_R_noTwo (X : ℝ) : ℝ :=
  ∑ N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, paper_r2 X N / (LeanLab.ChenExplicit.twinC * oddFac N)

/-- Dropping the factor 2 doubles R, so the sealed statement implies the
alternative reading with twice the constant. A factor 2 slip could only make
the sealed leaf weaker than the alternative, never false where it is true. -/
theorem paper_R_noTwo_eq (X : ℝ) : paper_R_noTwo X = 2 * paper_R X := by
  unfold paper_R_noTwo paper_R
  rw [mul_sum]
  apply sum_congr rfl
  intro N _
  by_cases h : LeanLab.ChenExplicit.twinC * oddFac N = 0
  · have : 2 * LeanLab.ChenExplicit.twinC * oddFac N = 0 := by rw [mul_assoc, h, mul_zero]
    rw [h, this]; simp
  · rw [mul_assoc]; field_simp

/-- Conditional: the sealed leaf gives the no-factor-2 reading with 0.956. -/
theorem noTwo_of_prop1 (h : Proposition1Flag1729) (X : ℝ) (hX : exp 67 ≤ X) :
    0.956 * X ^ 2 / Real.log X ≤ paper_R_noTwo X := by
  rw [paper_R_noTwo_eq]
  have := h X hX
  have e : 0.956 * X ^ 2 / Real.log X = 2 * (0.478 * X ^ 2 / Real.log X) := by ring
  rw [e]; linarith

end LeanLab.Ramare1995.Flag1729
