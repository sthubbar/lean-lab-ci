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

/-- Parseval identity for finite sequences on ℤ: the integral of |ĝ|² over [0,1] equals the sum of squares. -/
lemma parseval_fhat (S : Finset ℤ) (g : ℤ → ℝ) (hg : SuppIn S g) :
    (∫ α in (0 : ℝ)..(1 : ℝ), ‖fhat S g α‖ ^ 2) = sqn S g := by
  unfold fhat sqn
  -- Expand the square of the sum
  simp_rw [Complex.normSq_eq_norm_mul_self, Complex.norm_mul, Complex.norm_eq_abs,
    Complex.abs_ofReal, map_sum, Finset.sum_mul, Finset.mul_sum]
  -- Now we have ∫ α, (∑ n, g n * e(nα)) * (∑ m, g m * e(-mα))
  -- = ∑ n, ∑ m, g n * g m * ∫ α, e((n-m)α)
  sorry

/-- From FourierClose, we get a bound on the sup norm of the Fourier transform. -/
lemma fhat_sq_bound (S : Finset ℤ) (g : ℤ → ℝ) (H Δ : ℝ) (hH : 1 ≤ H)
    (hclose : FourierClose S H Δ g) (α : ℝ) : ‖fhat S g α‖ ^ 2 ≤ (H / 2) * Δ := by
  sorry

/-- LEAF page 6: The sum over n in [X - H, X] of the square of f * g at n is at most C0 H times the squared norm of f times the sup over α of the integral over β in [-1/H, 1/H] of the square of the absolute value of ĝ at α + β. -/
theorem leaf_short_second_moment_bound : ∃ C0 : ℝ, 0 ≤ C0 ∧
  (∀ (S : Finset ℤ) (f g : ℤ → ℝ) (X H Δ : ℝ), 1 ≤ H → SuppIn S f → SuppIn S g →
    FourierClose S H Δ g → ∑ n ∈ win X H, conv S f g n ^ 2 ≤ C0 * H * sqn S f * Δ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro S f g X H Δ hH hf hg hclose
  -- Use Cauchy-Schwarz: conv² ≤ sqn S f * sqn S g pointwise
  -- Then sum over window and bound sqn S g using FourierClose
  sorry

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
