import LeanLab.HelfgottMajor.Gaussian269
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Jensen

/-!
The elementary Mellin bound in P0014 page 29, display 3.76.
This is uniform in modulation but does not supply high ordinate exponential decay.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454j
open Real MeasureTheory Set
open LeanLab.HelfgottArcs Decomp269a

/-- The elementary Gamma bound used on P0014 page 27 and in display 3.76 on page 29. -/
theorem Gamma_le_inv (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : Real.Gamma x ≤ 1 / x := by
  have hg : Real.Gamma (x + 1) ≤ 1 := by
    have hh := Real.convexOn_Gamma.le_max_of_mem_Icc
      (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (2 : ℝ) ∈ Ioi 0)
      (show x + 1 ∈ Icc (1 : ℝ) 2 from ⟨by linarith, by linarith⟩)
    simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using hh
  rw [Real.Gamma_add_one hx.ne'] at hg
  apply (le_div_iff₀ hx).mpr
  nlinarith

/-- The Gamma expression is a modulation independent upper bound for the actual Mellin norm.
Source P0014 page 29, display 3.76, before the elementary Gamma estimate.
-/
theorem mellin_norm_le_Gamma (δ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    ‖gaussianMellin δ s‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (s.re / 2) * Real.Gamma (s.re / 2) := by
  have hg := Gaussian269.gaussian_moment s.re (1 / 2) hs (by norm_num)
  calc ‖gaussianMellin δ s‖ ≤
        ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * exp (-t ^ 2 / 2) :=
      Gaussian269.mellin_norm_le δ s
    _ = ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * exp (-((1 / 2) * t ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      congr 2
      ring
    _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (s.re / 2) * Real.Gamma (s.re / 2) := by
      simpa only [show (1 : ℝ) / (1 / 2) = 2 by norm_num] using hg

/-- The full elementary estimate printed in P0014 page 29, display 3.76.
The real part is positive and at most one. Modulation is arbitrary.
-/
theorem mellin_norm_le_power_div_re (δ : ℝ) (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    ‖gaussianMellin δ s‖ ≤ (2 : ℝ) ^ (s.re / 2) / s.re := by
  calc ‖gaussianMellin δ s‖ ≤
        (1 / 2 : ℝ) * (2 : ℝ) ^ (s.re / 2) * Real.Gamma (s.re / 2) :=
      mellin_norm_le_Gamma δ s hs
    _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (s.re / 2) * (1 / (s.re / 2)) :=
      mul_le_mul_of_nonneg_left (Gamma_le_inv _ (by linarith) (by linarith)) (by positivity)
    _ = (2 : ℝ) ^ (s.re / 2) / s.re := by ring

end LeanLab.HelfgottMajor.Decomp454j
