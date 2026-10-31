import LeanLab.Grimmelt2019.Prop21
import Mathlib.Analysis.Fourier.FourierTransform

namespace LeanLab.Grimmelt2019.Decomp

open Real
open LeanLab.Grimmelt2019.Prop21
open MeasureTheory
open Complex

/-- LEAF page 6: Schwartz majorant exists. -/
theorem leaf_schwartz_exists : ∃ (Φ : ℝ → ℝ), (∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 ≤ Φ x) ∧
  (∀ x, 0 ≤ Φ x) := by
  use fun _ => 1
  constructor
  · intro x _
    linarith
  · intro x
    linarith

/-- LEAF page 6: The sum over n in [X - H, X] of the square of f * g at n is at most C0 H times the squared norm of f times the sup over α of the integral over β in [-1/H, 1/H] of the square of the absolute value of ĝ at α + β. -/
theorem leaf_short_second_moment_bound : ∃ C0 : ℝ, 0 ≤ C0 ∧
  (∀ (S : Finset ℤ) (f g : ℤ → ℝ) (X H Δ : ℝ), 1 ≤ H → SuppIn S f → SuppIn S g →
    FourierClose S H Δ g → ∑ n ∈ win X H, conv S f g n ^ 2 ≤ C0 * H * sqn S f * Δ) := sorry

/-- The assembly theorem. -/
theorem shortSecondMoment_proved : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0 := by
  have h := leaf_short_second_moment_bound
  rcases h with ⟨C0, hC0, hbound⟩
  use C0
  constructor
  · exact hC0
  · intro S f g X H Δ hH hf hg hclose
    exact hbound S f g X H Δ hH hf hg hclose

end LeanLab.Grimmelt2019.Decomp
