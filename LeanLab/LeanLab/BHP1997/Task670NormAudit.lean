/-
P0069 Baker Harman Pintz 1997, page 43, Lemma 29 norm audit.
These auxiliary statements concern arbitrary functions. They do not refute the paper or the
sealed leaf, whose Dirichlet polynomial hypotheses carry extra information.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.BHP1997.Task670NormAudit
open MeasureTheory Set
/-- Lab audit of P0069 page 43. A unit tail has zero energy on the printed norm interval. -/
theorem tail_energy_printed {Y : ℝ} (hY : 0 < Y) :
    (∫ y in (Y/2)..(3*Y/2), ‖(Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℂ)) y‖ ^ 2) = 0 := by
  have hf : (fun y => ‖(Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℂ)) y‖ ^ 2) =
      (Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℝ)) := by
    funext y; by_cases hy : y ∈ Ioc (3*Y/2) (3*Y) <;> simp [hy]
  rw [hf, intervalIntegral.integral_of_le (by linarith),
    MeasureTheory.integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc]
  have hm : max (3*Y/2) (Y/2) = 3*Y/2 := max_eq_left (by linarith)
  have hn : min (3*Y) (3*Y/2) = 3*Y/2 := min_eq_right (by linarith)
  simp [hm, hn]
/-- Lab audit of P0069 page 43. The same unit tail has positive energy on the sealed interval. -/
theorem tail_energy_extended {Y : ℝ} (hY : 0 < Y) :
    (∫ y in (Y/2)..(3*Y), ‖(Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℂ)) y‖ ^ 2) = 3*Y/2 := by
  have hf : (fun y => ‖(Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℂ)) y‖ ^ 2) =
      (Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℝ)) := by
    funext y; by_cases hy : y ∈ Ioc (3*Y/2) (3*Y) <;> simp [hy]
  rw [hf, intervalIntegral.integral_of_le (by linarith),
    MeasureTheory.integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Ioc_inter_Ioc]
  have hm : max (3*Y/2) (Y/2) = 3*Y/2 := max_eq_left (by linarith)
  simp only [hm, min_self, MeasureTheory.setIntegral_const, Measure.real, Real.volume_Ioc,
    smul_eq_mul, mul_one, ENNReal.toReal_ofReal (by linarith : 0 ≤ 3*Y-3*Y/2)]
  ring
/-- The audit witness has integrable squared norm on every finite interval. -/
theorem tail_energy_integrable (Y a b : ℝ) : IntervalIntegrable
    (fun y => ‖(Ioc (3*Y/2) (3*Y)).indicator (fun _ => (1 : ℂ)) y‖ ^ 2) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const ?_ ?_
  · exact (((measurable_const.indicator measurableSet_Ioc).norm).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y ∈ Ioc (3*Y/2) (3*Y) <;> simp [hy]

/-- No constant extends the printed norm bound to the sealed interval for arbitrary integrable
functions. This is an audit of the lab interface, not a refutation of Lemma 29. -/
theorem no_generic_norm_extension {Y : ℝ} (hY : 0 < Y) (C : ℝ) :
    ∃ f : ℝ → ℂ, Measurable f ∧
      (∀ a b : ℝ, IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume a b) ∧
      (∫ y in (Y / 2)..(3 * Y), ‖f y‖ ^ 2) >
        C * (∫ y in (Y / 2)..(3 * Y / 2), ‖f y‖ ^ 2) := by
  refine ⟨(Ioc (3 * Y / 2) (3 * Y)).indicator (fun _ => (1 : ℂ)),
    measurable_const.indicator measurableSet_Ioc, tail_energy_integrable Y, ?_⟩
  rw [tail_energy_extended hY, tail_energy_printed hY, mul_zero]
  positivity

end LeanLab.BHP1997.Task670NormAudit
