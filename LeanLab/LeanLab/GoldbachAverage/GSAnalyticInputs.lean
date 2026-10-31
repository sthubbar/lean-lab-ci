import LeanLab.GoldbachAverage.InghamMeanSquare
import LeanLab.GoldbachAverage.ThetaLemma1

/-!
Named cited inputs from P0051, arXiv 2110.14250v2.
Pages 4, 6, 19 and 20 were read from the PDF in this run.
These are Prop definitions. None is asserted without a hypothesis.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.GSInputs
open MeasureTheory

/-- J x h is the short interval variance with lower limit zero. -/
def J (x h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2

/-- P0051 page 20 eq. 84, cited there from BHMS19 Lemma 8 at q equals one. -/
def BHMSShortIntervalVariance : Prop :=
  1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ x →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4

/-- P0051 page 19 eq. 82, the Grosswald refinement, stated as a cited input. -/
def GrosswaldPsiTheta : Prop :=
  1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ Theta

/-- P0051 page 20 eq. 85, the full variance conclusion. -/
def GSFullVariance : Prop :=
  1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ x →
      J x h ≤ C * h * x ^ (2 * Theta) * Real.log x ^ 4

/-- The paper's W uses the positive index series Psi minus I, not the zero index series. -/
def W (N : ℕ) (h : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..(1 / (2 * h)),
    ‖PsiGen (Real.exp (-(1 / (N : ℝ)))) α - IGen (Real.exp (-(1 / (N : ℝ)))) α‖ ^ 2

/-- P0051 Theorem 2 page 4 eq. 19, the Gallagher variance bound.
The two positive index series are represented with j plus one. -/
def GSGallagherVarianceBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 1 ≤ h → h ≤ N →
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) ∧
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * J (((j : ℝ) + 1) * N) h) ∧
    W N h ≤ C * (InghamTheta.H h / h ^ 2
      + (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) / (N : ℝ) ^ 2
      + (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * J (((j : ℝ) + 1) * N) h) / h ^ 2
      + N / h ^ 2)

/-- Under RH the strict theta premise of eq. 84 is false. -/
theorem bhms_short_variance_of_RH (hRH : RiemannHypothesis) : BHMSShortIntervalVariance := by
  intro hlo
  exact False.elim (not_lt_of_ge (GSCor2.Theta_le_of_RH hRH) hlo)

/-- Under RH the strict theta premise of eq. 82 is false. -/
theorem grosswald_of_RH (hRH : RiemannHypothesis) : GrosswaldPsiTheta := by
  intro hlo
  exact False.elim (not_lt_of_ge (GSCor2.Theta_le_of_RH hRH) hlo)

end LeanLab.GoldbachAverage.GSInputs
