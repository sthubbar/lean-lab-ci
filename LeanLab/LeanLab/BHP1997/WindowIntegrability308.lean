/-
BHP1997, page 3, condition iv. The finite moving-window sums have genuine square integrals.
The search reuses measurableSet_le, Measurable.ite and IntegrableOn.of_bound.
No mean square estimate is asserted here.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Task308
open MeasureTheory Set Classical

/-- Page 3, condition iv. A finite coefficient sum in the moving window is measurable,
including either sign of z and either order of the integration endpoints. -/
theorem window_sum_measurable (S : Finset ℕ) (c : ℕ → ℂ) (z : ℝ) :
    Measurable (fun y : ℝ => ∑ m ∈ S.filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m) := by
  have he : (fun y : ℝ => ∑ m ∈ S.filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m) =
      fun y : ℝ => ∑ m ∈ S,
        if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c m else 0 := by
    funext y
    exact Finset.sum_filter _ _
  rw [he]
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.ite
    ((measurableSet_le measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_id.add (measurable_id.mul_const z))))
    measurable_const measurable_const

/-- Page 3, condition iv. The squared norm of the finite moving-window sum is
interval integrable. This certifies integrability only, with no analytic saving. -/
theorem window_sum_sq_intervalIntegrable (S : Finset ℕ) (c : ℕ → ℂ)
    (z a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => ‖∑ m ∈ S.filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m‖ ^ 2) volume a b := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top)
    (((window_sum_measurable S c z).norm.pow_const 2).aestronglyMeasurable)
    ((∑ m ∈ S, ‖c m‖) ^ 2)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    ‖∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m‖ ≤
        ∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ‖c m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ‖c m‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m hm hnot => norm_nonneg _)

end LeanLab.BHP1997.Task308
