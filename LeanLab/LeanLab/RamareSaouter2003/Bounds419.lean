import LeanLab.RamareSaouter2003.Circle419

/-!
Backlund p. 362, display 54, the logarithmic zeta bound on the line of real part one.
PNTPort.ZetaZeros.Count.norm_zeta_le instead supplies two plus the norm on that line.
This comparison records why that coarse bound does not close the circle growth leaf.
It is a limitation of a proof route and asserts no paper error.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Bounds419

/-- Backlund p. 362, display 54, compared with the existing PNTPort coarse bound.
Even enlarging the logarithmic height by the circle radius leaves a smaller bound. -/
theorem coarse_bound_too_large (T : ℝ) (hT : 1400 ≤ T) :
    Real.log (T + 1.32) < 2 + ‖(1 : ℂ) + T * Complex.I‖ := by
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < T + 1.32)
  have hi := Complex.im_le_norm ((1 : ℂ) + T * Complex.I)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at hi
  linarith

end LeanLab.RamareSaouter2003.Bounds419
#print axioms LeanLab.RamareSaouter2003.Bounds419.coarse_bound_too_large
