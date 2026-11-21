import LeanLab.HelfgottMajor.ContourKernel669
import LeanLab.HelfgottMajor.DQSaddleSegmentBound

/-!
The original two contour bound statements, with their statements unchanged.
Shared definitions and proved geometric lemmas moved verbatim to ContourKernel669.
The saddle proof reuses the assembly supplied by the requested base branch.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp639Contour
open Real MeasureTheory Set SplitGaussian123 Decomp511a Filter
open scoped Topology

/-- LEAF: P0014 page 23, displays 3.56 and 3.57.
The central limacon integral has the printed main coefficient and saddle exponent.
OPEN. This requires the quantitative phase and arc length estimates of Section 3.7. -/
theorem saddle_segment_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
      exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  exact DQSaddleSegmentBound.saddle_segment_bound_of_leaves δ s hσ0 hσ1 ht hsign

/-- LEAF: P0014 pages 24 to 25, displays 3.59 to 3.63 and the bound after 3.63.
Integration by parts on C1 gives the uniform first coefficient on the critical strip.
OPEN. The phase cost uses A.33 and the radius bound of display 3.61. -/
theorem initial_segment_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| *
      exp (-0.4798 * |s.im|) := by
  sorry

end LeanLab.HelfgottMajor.Decomp639Contour

#print axioms LeanLab.HelfgottMajor.Decomp639Contour.saddle_segment_bound
