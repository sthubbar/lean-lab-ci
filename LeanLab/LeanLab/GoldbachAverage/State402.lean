import Mathlib

/-!
Goldston and Suriajaya, arXiv 2110.14250v2 page 12 eq. 58 and page 15 Lemma 3 eq. 71.
The comparison is stated at the paper's application f equal to psi minus the identity.
Its written proof is on page 19. Decomp402e proves this proposition.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.State402
open MeasureTheory

/-- The relative short interval variance of P0051 page 12 eq. 58. -/
def Jrelative (x δ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (Chebyshev.psi ((1 + δ) * t) - Chebyshev.psi t - δ * t) ^ 2

/-- PAPER STATEMENT. P0051 page 15 Lemma 3 eq. 71, at f t equal to psi t minus t.
The exact factor is two x over h. Its written change of variables proof is on page 19.
This new paper proposition requires Claude statement review before merge. -/
def SaffariVaughanPsiComparison : Prop :=
  ∀ x h : ℝ, 1 ≤ h → h ≤ x / 4 →
    (∫ t in (x / 2)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
      (2 * x / h) * ∫ δ in (0 : ℝ)..(8 * h / x), Jrelative x δ

/-- The zero width instance of the relative variance in P0051 page 12 eq. 58. -/
theorem Jrelative_zero (x : ℝ) : Jrelative x 0 = 0 := by
  simp [Jrelative]

/-- The variance in P0051 page 12 eq. 58 is nonnegative on every nonnegative prefix. -/
theorem Jrelative_nonneg {x δ : ℝ} (hx : 0 ≤ x) : 0 ≤ Jrelative x δ := by
  exact intervalIntegral.integral_nonneg hx (fun _ _ => sq_nonneg _)

end LeanLab.GoldbachAverage.State402
