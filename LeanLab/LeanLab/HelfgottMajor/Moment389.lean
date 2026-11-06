import LeanLab.HelfgottMajor.HalfMoment389
import LeanLab.HelfgottMajor.Gaussian269

/-!
The remaining elementary Gaussian power recurrence in P0014 page 43, display 4.42.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Moment389
open Real MeasureTheory Set

/-- The three halves moment is one half of the minus one half moment.
This is Gamma of five quarters equals one quarter times Gamma of one quarter in display 4.42.
-/
theorem three_halves_moment_eq_half :
    (∫ t in Ioi (0 : ℝ), t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2)) =
      (1 / 2 : ℝ) * ∫ t in Ioi (0 : ℝ),
        t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) := by
  have h0 := Gaussian269.gaussian_moment (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  have h1 := Gaussian269.gaussian_moment (5 / 2) (1 / 2) (by norm_num) (by norm_num)
  have hi : (fun t : ℝ => t ^ ((5 / 2 : ℝ) - 1) * exp (-((1 / 2 : ℝ) * t ^ 2))) =
      fun t : ℝ => t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2) := by
    funext t
    rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num]
    rw [show -((1 / 2 : ℝ) * t ^ 2) = -t ^ 2 / 2 by ring]
  have hi0 : (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * exp (-((1 / 2 : ℝ) * t ^ 2))) =
      fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) * exp (-t ^ 2 / 2) := by
    funext t
    rw [show -((1 / 2 : ℝ) * t ^ 2) = -t ^ 2 / 2 by ring]
  rw [hi] at h1
  rw [hi0] at h0
  norm_num only [one_div_div, div_self, show (2 : ℝ) ≠ 0 by norm_num,
    show (5 / 2 : ℝ) / 2 = 5 / 4 by norm_num,
    show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] at h0 h1
  have hg : Gamma (5 / 4) = (1 / 4 : ℝ) * Gamma (1 / 4) := by
    rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Gamma_add_one (by norm_num)]
  have hp : (2 : ℝ) ^ (5 / 4 : ℝ) = 2 * 2 ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, rpow_add (by norm_num), rpow_one]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  rw [h1, h0, hg, hp]
  ring

/-- The Gaussian three halves power moment is at most 1.07791, as in display 4.42 on page 43. -/
theorem three_halves_moment_bound :
    (∫ t in Ioi (0 : ℝ), t ^ (3 / 2 : ℝ) * exp (-t ^ 2 / 2)) ≤ 1.07791 := by
  rw [three_halves_moment_eq_half]
  have h := HalfMoment389.gaussian_half_moment_bound
  linarith

end LeanLab.HelfgottMajor.Moment389
