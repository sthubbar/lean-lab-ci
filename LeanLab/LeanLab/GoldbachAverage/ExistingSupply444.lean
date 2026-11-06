import LeanLab.GoldbachAverage.Decomp402b
import LeanLab.GoldbachAverage.Decomp402d
import LeanLab.GoldbachAverage.BoundedWindow402

/-!
Exact bridges for source leaves already proved elsewhere in this folder.
Sources: BSP page 5 pair averaging, P0051 page 9 spatial split,
and the bounded window extension of BHMS page 17.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ExistingSupply444
open MeasureTheory
open Decomp287b Decomp287c GallagherReduction124 I2Bound124

/-- BSP page 5 pair averaging, supplied by the existing finite proof.
CONDITIONAL ON the displayed progression lower bound. -/
theorem progression_pair_average_proved (x q : ℕ) (hx : 2 ≤ x) (hq : 0 < q) (hqx : q ≤ x)
    (hAP : ∀ a : ℕ, a < q → Nat.Coprime a q →
      (x : ℝ) / (2 * Nat.totient q) ≤ progressionMass x q a) :
    ∃ N : ℕ, 2 * x < N ∧ N ≤ 4 * x ∧
      (x : ℝ) * q / (16 * Nat.totient q) ≤ G N := by
  exact Decomp402b.progression_pair_average_assembled x q hx hq hqx hAP

example : type_of% Decomp287c.progression_pair_average = type_of% progression_pair_average_proved := rfl

/-- P0051 page 9 eqs. 48 and 49, supplied by the existing exact spatial split. -/
theorem moving_mass_split_proved (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 1 ≤ h) (hhN : h ≤ N) :
    (∫ x : ℝ, ‖movingSum (coefficients N) x h‖ ^ 2) = I1 N h + I2 N h := by
  exact Decomp402d.moving_mass_split_assembled N hN h hh hhN

example : type_of% Decomp287b.moving_mass_split = type_of% moving_mass_split_proved := rfl

/-- BHMS page 17 bounded window extension, supplied by the existing finite psi proof. -/
theorem bounded_window_variance_proved : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ 2 →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        C * x * Real.log x ^ 4 := by
  exact BoundedWindow402.bounded_window_variance_proved

example : type_of% Decomp287d.bounded_window_variance = type_of% bounded_window_variance_proved := rfl

end LeanLab.GoldbachAverage.ExistingSupply444
