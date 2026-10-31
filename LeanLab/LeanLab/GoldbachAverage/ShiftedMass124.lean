import LeanLab.GoldbachAverage.WeightedMass124

/-!
The shifted endpoint square integral after P0051 page 10 eq. 55.
Source: arXiv 2110.14250v2 page 11.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ShiftedMass124
open MeasureTheory Set
open FloorVariance82 WeightedMass124 Sliding124

/-- Shifting the endpoint changes its exponential weight by the factor exp of two h over N.
Source: P0051 page 11 shifted endpoint term. -/
theorem shift_weight_identity (N : ℕ) (x h : ℝ) :
    psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N) =
      Real.exp (2 * h / N) *
        (psiFloorError (x + h) ^ 2 * Real.exp (-2 * (x + h) / N)) := by
  have he : Real.exp (2 * h / N) * Real.exp (-2 * (x + h) / N) =
      Real.exp (-2 * x / N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- The shifted weighted square has finite mass on the positive half line.
Source: P0051 page 11, second term in the first display. -/
theorem shifted_R_square_integrable (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun x : ℝ => psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N)) (Ioi 0) := by
  have hi := positive_shift_integrable (weighted_R_square_integrable N hN) hh
  have hc : IntegrableOn (fun x : ℝ => Real.exp (2 * h / N) *
      (psiFloorError (x + h) ^ 2 * Real.exp (-2 * (x + h) / N))) (Ioi 0) :=
    hi.const_mul (Real.exp (2 * h / N))
  refine hc.congr_fun ?_ measurableSet_Ioi
  intro x _
  exact (shift_weight_identity N x h).symm

/-- LEAF. P0051 page 11, absorb the shifted endpoint weight for h at most N.
The explicit cost is exp two. -/
theorem shifted_R_mass_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ}
    (hh : 0 ≤ h) (hhN : h ≤ N) :
    (∫ x : ℝ in Ioi 0, psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N)) ≤
      Real.exp 2 * ∫ u : ℝ in Ioi 0, psiFloorError u ^ 2 * Real.exp (-2 * u / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (fun x : ℝ => psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N)) =
      (fun x : ℝ => Real.exp (2 * h / N) *
        (psiFloorError (x + h) ^ 2 * Real.exp (-2 * (x + h) / N))) :=
    funext (fun x => shift_weight_identity N x h)
  rw [heq, integral_const_mul]
  have hc : Real.exp (2 * h / N) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hN0).mpr
    linarith
  have hs := positive_shift_integral_le (weighted_R_square_integrable N hN)
    (fun u _ => by positivity) hh
  exact mul_le_mul hc hs (integral_nonneg (fun _ => by positivity)) (Real.exp_pos 2).le

end LeanLab.GoldbachAverage.ShiftedMass124
