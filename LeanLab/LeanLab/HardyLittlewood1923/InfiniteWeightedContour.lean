import LeanLab.HardyLittlewood1923.WeightedHorizontal

/-!
AI wrote this Lean code for CODEX task52.
The exponential weighted contour shift serves P0004 page 11 equation 2.416.
The contour stays to the right of every zero on the paper's Hypothesis R.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace LeanLab.HardyLittlewood1923.Task52

/-- The infinite weighted contour shift for primitive nonprincipal characters. -/
theorem weightedSum_shift_nonprincipal {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    {σ : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) (hσ1 : σ ≠ 1)
    {z : ℂ} (hz : 0 < z.re) :
    weightedSum χ z = (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel χ z ((σ : ℂ) + t * I)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hleft := weightedKernel_integrable hZ hχ hσ h1 h2 hσ1 hz
  have hright := weightedKernel_integrable hZ hχ (lt_of_lt_of_le hσ h2)
    (by norm_num : (1 : ℝ) / 2 ≤ 3 / 2) (by norm_num : (3 : ℝ) / 2 ≤ 3 / 2)
    (by norm_num : (3 : ℝ) / 2 ≠ 1) hz
  obtain ⟨hlo, hhi⟩ := weighted_horizontal_decay hZ hχ h2 h1
    (by norm_num : (3 : ℝ) / 2 ≤ 3 / 2) hσ hz
  have hr : ∀ T : ℝ, VIntegral (weightedKernel χ z) (3 / 2) (-T) T =
      VIntegral (weightedKernel χ z) σ (-T) T - HIntegral (weightedKernel χ z) σ (3 / 2) (-T) +
        HIntegral (weightedKernel χ z) σ (3 / 2) T := by
    intro T
    exact weighted_rectangle_shift_of_noZeros hZ hχ hq hz0 (by linarith) hσ h2
  have he := vertical_eq_of_rectangle hr hleft hright hlo hhi
  rw [weightedSum_mellin_right χ (σ := 3 / 2) (by norm_num) (by norm_num) hz, he]

/-- The contour identity on the previously open lower range of Theta. -/
theorem weightedSum_shift_lower_range {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (hΘ : Θ < 47 / 64)
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1 - Θ) {z : ℂ} (hz : 0 < z.re) :
    weightedSum χ z = (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel χ z (((Θ + η : ℝ) : ℂ) + t * I)) := by
  exact weightedSum_shift_nonprincipal hZ hχ hq (by linarith) (by linarith)
    (by linarith) (by linarith) hz

#print axioms weightedSum_shift_nonprincipal
#print axioms weightedSum_shift_lower_range

end LeanLab.HardyLittlewood1923.Task52
