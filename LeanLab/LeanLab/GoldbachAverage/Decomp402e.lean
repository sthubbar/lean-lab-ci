import LeanLab.GoldbachAverage.State402
import LeanLab.GoldbachAverage.Rectangle402
import LeanLab.GoldbachAverage.Translated402

/-!
Goldston and Suriajaya, arXiv 2110.14250v2 page 19 proof of Lemma 3.
The additive rectangle comparison and its multiplicative change of variables are separate leaves.
The function is the paper's application psi minus the identity.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402e
open MeasureTheory
open State402

/-- The additive rectangle R in the P0051 page 19 proof of eq. 71. -/
def rectangleMass (x h : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * h), ∫ y in (x / 4)..x,
    (Chebyshev.psi (y + u) - Chebyshev.psi y - u) ^ 2

/-- LEAF. P0051 page 19 first five displays in the proof of Lemma 3.
Average translation t equal to y plus u over zero to h, apply the square triangle bound,
and enlarge both y ranges to the common interval x over four to x. -/
theorem translated_square_to_rectangle (x h : ℝ) (hh : 1 ≤ h) (hhx : h ≤ x / 4) :
    (∫ t in (x / 2)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
      (2 / h) * rectangleMass x h := by
  simpa only [rectangleMass] using Translated402.translated_square_to_rectangle_proved x h hh hhx

/-- LEAF. P0051 page 19 final three displays in the proof of Lemma 3.
Use u equal to delta times y. Bound its Jacobian y by x, enlarge delta to eight h over x,
then interchange the nonnegative double integral and enlarge the y interval to zero to x. -/
theorem rectangle_to_relative (x h : ℝ) (hh : 1 ≤ h) (hhx : h ≤ x / 4) :
    rectangleMass x h ≤ x * ∫ δ in (0 : ℝ)..(8 * h / x), Jrelative x δ := by
  simpa only [rectangleMass] using Rectangle402.rectangle_to_relative_proved x h hh hhx

/-- The exact paper comparison at psi minus the identity follows from the two rectangle leaves.
Both rectangle comparisons are proved from compact integral identities. -/
theorem saffari_vaughan_assembled : SaffariVaughanPsiComparison := by
  intro x h hh hhx
  have hh0 : 0 < h := by linarith
  calc (∫ t in (x / 2)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2)
      ≤ (2 / h) * rectangleMass x h := translated_square_to_rectangle x h hh hhx
    _ ≤ (2 / h) * (x * ∫ δ in (0 : ℝ)..(8 * h / x), Jrelative x δ) :=
      mul_le_mul_of_nonneg_left (rectangle_to_relative x h hh hhx) (by positivity)
    _ = (2 * x / h) * ∫ δ in (0 : ℝ)..(8 * h / x), Jrelative x δ := by ring

end LeanLab.GoldbachAverage.Decomp402e
