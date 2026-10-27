/-
A concrete normalized even smooth major weight for Definition 7.1, page 26.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The standard even smooth bump with inner radius one and outer radius two. -/
def majorBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The bump has strictly positive total mass. -/
theorem majorBump_integral_pos : 0 < ∫ x : ℝ, majorBump x := by
  apply majorBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    majorBump.hasCompactSupport majorBump.nonneg' (x := 0)
  rw [majorBump.one_of_mem_closedBall]
  · norm_num
  · simp [majorBump]

/-- Normalize the fixed bump to have integral one. -/
noncomputable def majorWeight (x : ℝ) : ℝ :=
  (∫ y : ℝ, majorBump y)⁻¹ * majorBump x

/-- The hypotheses in the paper's smooth major weight class have a concrete instance. -/
theorem majorWeight_isMajorWeight : IsMajorWeight majorWeight := by
  have hp := majorBump_integral_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul majorBump.contDiff
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hp.le) majorBump.nonneg
  · intro x hx
    have hb : majorBump x ≠ 0 := by
      intro hb
      exact hx (by simp [majorWeight, hb])
    have hball : x ∈ Metric.ball (0 : ℝ) 2 := by
      have hm : x ∈ Function.support (majorBump : ℝ → ℝ) := hb
      rw [majorBump.support_eq] at hm
      exact hm
    have ha : |x| < 2 := by simpa [Real.dist_eq] using hball
    exact ⟨by linarith [(abs_lt.mp ha).1], (abs_lt.mp ha).2.le⟩
  · refine ⟨(∫ y : ℝ, majorBump y)⁻¹, inv_pos.mpr hp, ?_⟩
    intro x hx
    have hm : x ∈ Metric.closedBall (0 : ℝ) majorBump.rIn := by
      change dist x 0 ≤ 1
      simpa [Real.dist_eq] using abs_le.mpr hx
    simp only [majorWeight, majorBump.one_of_mem_closedBall hm, mul_one]
  · unfold majorWeight
    rw [integral_const_mul, inv_mul_cancel₀ hp.ne']
  · intro x
    simp only [majorWeight, majorBump.neg]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.majorBump_integral_pos
#print axioms LeanLab.BhowmikGrimmelt2026.majorWeight_isMajorWeight
