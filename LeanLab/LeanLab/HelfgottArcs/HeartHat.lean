/-
The one-sided Gaussian's Fourier transform at 0, against the remark in 1305.2897
"Of course, η̂_♥(−δ) is just √(2π)e^{−2π²δ²}".
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.HelfgottArcs.Statements

namespace LeanLab.HelfgottArcs
open MeasureTheory Set

theorem etaHeart_eq_indicator :
    etaHeart = (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-(1 / 2) * t ^ 2)) := by
  funext t
  unfold etaHeart
  by_cases ht : 0 < t
  · rw [if_pos ht, indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]; ring_nf
  · rw [if_neg ht, indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]

/-- With weights on `(0, ∞)` extended by 0, `η̂_♥(0) = √(2π)/2`, half the value
`√(2π)` that the remark gives at `δ = 0`. -/
theorem fhat_etaHeart_zero : fhat etaHeart 0 = ((Real.sqrt (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  unfold fhat
  have he : ∀ y : ℝ, e (-(y * 0)) = 1 := by intro y; simp [e]
  simp only [he, one_mul]
  rw [integral_complex_ofReal, etaHeart_eq_indicator, integral_indicator measurableSet_Ioi,
    integral_gaussian_Ioi]
  congr 2
  rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring]

/-- So the remark's value is wrong for the one-sided weight. -/
theorem remark_fails_at_zero :
    fhat etaHeart 0 ≠ ((Real.sqrt (2 * Real.pi) * Real.exp (-2 * Real.pi ^ 2 * 0 ^ 2) : ℝ) : ℂ) := by
  rw [fhat_etaHeart_zero]
  intro h
  have h' := Complex.ofReal_injective h
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  simp at h'
  have : 0 < Real.sqrt 2 * Real.sqrt Real.pi := by positivity
  linarith

end LeanLab.HelfgottArcs
