/-
The short interval variance on page 22, with H subtracted after the prime sum.
The explicit parse audit confirms that the existing V already has this grouping.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- The variance from page 22, with the expected count H outside the finite sum. -/
noncomputable def Vshort (X H : ℝ) : ℝ :=
  ∫ x in X..(2 * X),
    ((∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, vonMangoldt n) - H) ^ 2

/-- The variance is nonnegative when its integration interval is positively oriented. -/
theorem Vshort_nonneg {X H : ℝ} (hX : 0 ≤ X) : 0 ≤ Vshort X H := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  exact sq_nonneg _

/-- At interval length zero the correctly grouped variance vanishes. -/
theorem Vshort_zero (X : ℝ) : Vshort X 0 = 0 := by
  simp [Vshort]

/-- The explicit grouping agrees with the existing V definition. -/
theorem Vshort_eq_V (X H : ℝ) : Vshort X H = V X H := rfl

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.Vshort_nonneg
#print axioms LeanLab.BhowmikGrimmelt2026.Vshort_zero
#print axioms LeanLab.BhowmikGrimmelt2026.Vshort_eq_V
