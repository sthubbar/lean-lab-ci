/-
P0079 page 9, display 32, decay of the continuous prime model.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ModelExpansion396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. Direct integration gives the continuous
prime model as an endpoint difference divided by its frequency. -/
theorem continuousPrime_endpoints396 (ε X α : ℝ) (hα : α ≠ 0) :
    continuousPrime353 ε X α =
      (character293 (X * α) - character293 ((ε * X) * α)) /
        (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
  let c : ℂ := ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα)) Complex.I_ne_zero
  have he (t : ℝ) : character293 (t * α) = Complex.exp (c * t) := by
    unfold character293
    congr 1
    dsimp [c]
    push_cast
    ring
  unfold continuousPrime353
  simp_rw [he]
  exact integral_exp_mul_complex hc

/-- P0079 page 9, display 32. Away from zero, the continuous prime
model norm is at most the reciprocal of pi times absolute frequency. -/
theorem continuousPrime_decay396 (ε X α : ℝ) (hα : α ≠ 0) :
    ‖continuousPrime353 ε X α‖ ≤ 1 / (Real.pi * |α|) := by
  rw [continuousPrime_endpoints396 ε X α hα, norm_div]
  have hc : ‖(((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.pi * |α| := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hc]
  have hn : ‖character293 (X * α) - character293 ((ε * X) * α)‖ ≤ 2 := by
    calc
      _ ≤ ‖character293 (X * α)‖ + ‖character293 ((ε * X) * α)‖ := norm_sub_le _ _
      _ = _ := by rw [character_norm293, character_norm293]; norm_num
  calc
    _ ≤ 2 / (2 * Real.pi * |α|) := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by ring

end LeanLab.LZPowersOfTwo
