/-
Helfgott https://arxiv.org/abs/1305.2897v4 pages 76 and 77, equations B.34 to B.38.
Separate the band limited approximation from the elementary Gaussian norm step.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Statements
import LeanLab.Ternary.Decomp379b
import LeanLab.Helfgott2013.SectionSevenI
import LeanLab.Helfgott2013.Conclusion

namespace LeanLab.Ternary.Task420
open Real

/-- The unsmoothed compact Gaussian bump has absolute value at most one.
Helfgott major arcs page 76 equation B.34, the derivative computation is replaced
by the identity t times two minus t equals one minus the square of t minus one. -/
theorem hfun_gaussian_bump_le {t : ℝ} (ht : 0 ≤ t) :
    |LeanLab.HelfgottArcs.hfun t * t * Real.exp (-t ^ 2 / 2)| ≤ 1 := by
  unfold LeanLab.HelfgottArcs.hfun
  split_ifs with h
  · have hp0 : 0 ≤ t * (2 - t) := mul_nonneg ht (by linarith [h.2])
    have hp1 : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have hp3 : (t * (2 - t)) ^ 3 ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ hp0 hp1 3
    have he : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (t - 1)]
    have hid : t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) * t *
        Real.exp (-t ^ 2 / 2) = (t * (2 - t)) ^ 3 *
          Real.exp (-(t - 1) ^ 2 / 2) := by
      calc
        _ = (t * (2 - t)) ^ 3 * (Real.exp (t - 1 / 2) * Real.exp (-t ^ 2 / 2)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    rw [hid, abs_of_nonneg (by positivity)]
    simpa using mul_le_mul hp3 he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1 ^ 3)
  · simp

/-- The derivative norm coefficient times the Gaussian supremum is below its printed rounding.
Helfgott major arcs page 77 equation B.38. -/
theorem gaussian_derivative_rounding :
    (2 / Real.exp 1) * (2.80582038 : ℝ) ≤ 2.06440727 := by
  have he := Real.exp_one_gt_d9
  have he0 := Real.exp_pos (1 : ℝ)
  calc
    _ = (2 * 2.80582038) / Real.exp 1 := by ring
    _ ≤ _ := (div_le_iff₀ he0).mpr (by nlinarith)

/-- The coarse convergence bound cannot supply the sharp smoothing norm even at t one.
This is a limitation of that elementary majorant, not an error in the paper.
Compare the page 56 smoothing definition with the page 77 equation B.38 target. -/
theorem coarse_gaussian_bound_not_sharp :
    (1.079955 : ℝ) <
      (32 * Real.exp (3 / 2) * (200 / Real.pi)) * Real.exp (-(1 : ℝ) / 2) := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hp := Real.pi_lt_four
  have h : (1600 : ℝ) ≤ 6400 * Real.exp 1 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith
  calc
    _ < (1600 : ℝ) := by norm_num
    _ ≤ 6400 * Real.exp 1 / Real.pi := h
    _ = _ := by
      rw [show (32 * Real.exp (3 / 2) * (200 / Real.pi)) * Real.exp (-(1 : ℝ) / 2) =
        (6400 / Real.pi) * (Real.exp (3 / 2) * Real.exp (-(1 : ℝ) / 2)) by ring,
        ← Real.exp_add]
      norm_num
      ring

/-- LEAF. The band limited compact factor approximates h with linear pointwise error.
Helfgott major arcs page 76 equation B.35 and page 77 equations B.36 and B.37.
Integration by parts against the sine integral gives B.36. The derivative norm
bound B.37 is rounded upwards to 2.80582038. The Gaussian factor is absent. -/
theorem hfun_bandlimited_error {t : ℝ} (ht : 0 < t) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.hfun
        (LeanLab.HelfgottArcs.FH 200) t - LeanLab.HelfgottArcs.hfun t| ≤
      t * 2.80582038 * ((1 + 4 / Real.pi * Real.log 200) / 200) := by
  sorry

/-- The sharp eta plus norm is supplied by the independent Fourier proof.
Helfgott major arcs page 77 equation B.38 and ternary page 56 equation 7.3.
The proved supply in Decomp379b avoids the older pointwise error input. -/
theorem etaPlus_abs_le_from_bandlimited_error (t : ℝ) :
    |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ) := by
  exact EtaBound379.etaPlus_abs_le t


end LeanLab.Ternary.Task420
