import LeanLab.GoldbachAverage.Decomp444a
import LeanLab.GoldbachAverage.GSAnalyticInputs

/-!
Concrete normalization and vacuity checks for the task444 supplies.
Sources: GY page 4 eq. 4.1 and GS page 20 eq. 84.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Instances444
open MeasureTheory
open Decomp287b

/-- GY page 4 eq. 4.1 has nonzero mass one for a single unit coefficient and width one. -/
theorem unit_plancherel_mass :
    Integrable (fun α : ℝ => Real.sinc (Real.pi * α) ^ 2 *
      ‖fourierSeries (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) α‖ ^ 2) ∧
    (∫ α : ℝ, Real.sinc (Real.pi * α) ^ 2 *
      ‖fourierSeries (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) α‖ ^ 2) = 1 ∧
    (∫ x : ℝ, ‖movingSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) x 1‖ ^ 2) = 1 := by
  classical
  let a : ℕ → ℂ := fun n => if n = 1 then 1 else 0
  have ha : Summable (fun n => ‖a n‖) := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    have hne : n ≠ 1 := by simpa using hn
    simp [a, hne]
  have hi := MovingIntegrability402.moving_square_integrable_proved a ha 1 (by norm_num)
  have hm := MovingIntegrability402.unit_window_mass 1 (by norm_num)
  have hp := Decomp444a.moving_plancherel_proved a ha 1 (by norm_num) hi
  refine ⟨?_, ?_, hm⟩
  · simpa only [mul_one] using hp.1
  · simpa only [a, mul_one, one_pow, div_one, hm] using hp.2

/-- GS page 20 eq. 84 has a false strict Theta premise under RH.
This is a vacuity check and does not assert RH or a nonvacuous strict strip. -/
theorem strict_Theta_false_under_RH (hRH : RiemannHypothesis) :
    ¬ (1 / 2 < Theta ∧ Theta < 1) := by
  intro h
  exact not_lt_of_ge (GSCor2.Theta_le_of_RH hRH) h.1

end LeanLab.GoldbachAverage.Instances444
