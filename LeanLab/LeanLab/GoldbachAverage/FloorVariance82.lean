import LeanLab.GoldbachAverage.Variance82

/-!
The floor error comparisons in P0051 pages 10 and 11, eqs. 50 to 52.
These are elementary leaves of the remaining Theorem 2 input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.FloorVariance82
open MeasureTheory Filter

/-- The counting function R of P0051 eq. 50, expressed using the fractional part. -/
def psiFloorError (t : ℝ) : ℝ := Chebyshev.psi t - t + Int.fract t

/-- The fractional part expression equals psi minus the integer floor, eq. 50 page 10. -/
theorem psiFloorError_eq (t : ℝ) : psiFloorError t = Chebyshev.psi t - (⌊t⌋ : ℝ) := by
  simp only [psiFloorError, Int.fract]
  ring

/-- The counting function in eq. 50 is measurable. -/
theorem measurable_psiFloorError : Measurable psiFloorError := by
  exact (Chebyshev.psi_mono.measurable.sub measurable_id).add measurable_fract

/-- LEAF. P0051 page 10 eq. 51, with explicit constants two. -/
theorem floor_prefix_bound {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, psiFloorError t ^ 2) ≤ 2 * InghamTheta.H x + 2 * x := by
  have hpt : ∀ t : ℝ, psiFloorError t ^ 2 ≤ 2 * (Chebyshev.psi t - t) ^ 2 + 2 := by
    intro t
    have h0 := Int.fract_nonneg t
    have h1 := Int.fract_lt_one t
    have hsq : Int.fract t ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1.le)]
    dsimp [psiFloorError]
    nlinarith [sq_nonneg ((Chebyshev.psi t - t) - Int.fract t)]
  have hg : IntervalIntegrable (fun t : ℝ => 2 * (Chebyshev.psi t - t) ^ 2 + 2) volume 0 x :=
    ((GSInputs.psi_error_square_integrable hx).const_mul 2).add intervalIntegrable_const
  have hi : IntervalIntegrable (fun t : ℝ => psiFloorError t ^ 2) volume 0 x := by
    refine hg.mono_fun' (measurable_psiFloorError.pow_const 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt t
  have hm := intervalIntegral.integral_mono_on hx hi hg (fun t _ => hpt t)
  rw [intervalIntegral.integral_add ((GSInputs.psi_error_square_integrable hx).const_mul 2)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at hm
  simpa only [InghamTheta.H, sub_zero, mul_comm] using hm

/-- LEAF. P0051 page 10 eq. 52, with explicit constants two. -/
theorem floor_increment_bound {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..x, (psiFloorError (t + h) - psiFloorError t) ^ 2) ≤
      2 * GSInputs.J x h + 2 * x := by
  have hpt : ∀ t : ℝ, (psiFloorError (t + h) - psiFloorError t) ^ 2 ≤
      2 * (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 + 2 := by
    intro t
    have h0 := Int.fract_nonneg t
    have h1 := Int.fract_lt_one t
    have h2 := Int.fract_nonneg (t + h)
    have h3 := Int.fract_lt_one (t + h)
    have hsq : (Int.fract (t + h) - Int.fract t) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg
        (show 0 ≤ 1 - (Int.fract (t + h) - Int.fract t) by linarith)
        (show 0 ≤ 1 + (Int.fract (t + h) - Int.fract t) by linarith)]
    dsimp [psiFloorError]
    nlinarith [sq_nonneg ((Chebyshev.psi (t + h) - Chebyshev.psi t - h) -
      (Int.fract (t + h) - Int.fract t))]
  have hj := Decomp82.short_error_integrable hx hh
  have hg : IntervalIntegrable
      (fun t : ℝ => 2 * (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 + 2) volume 0 x :=
    (hj.const_mul 2).add intervalIntegrable_const
  have hm : Measurable (fun t : ℝ => (psiFloorError (t + h) - psiFloorError t) ^ 2) :=
    ((measurable_psiFloorError.comp (measurable_id.add_const h)).sub
      measurable_psiFloorError).pow_const 2
  have hi : IntervalIntegrable (fun t : ℝ => (psiFloorError (t + h) - psiFloorError t) ^ 2)
      volume 0 x := by
    refine hg.mono_fun' hm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt t
  have hb := intervalIntegral.integral_mono_on hx hi hg (fun t _ => hpt t)
  rw [intervalIntegral.integral_add (hj.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hb
  simpa only [GSInputs.J, sub_zero, mul_comm] using hb

end LeanLab.GoldbachAverage.FloorVariance82
