import LeanLab.Zhao2025.ExpPair
import LeanLab.Zhao2025.BMonotone

/-!
The exponential pair has an elementary endpoint integral.
Source: an elementary helper for Zhao 2025 display 2.23, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The integral of the symmetric exponential pair. -/
theorem exp_pair_integral (t a : ℝ) (ha : a ≠ 0) :
    (∫ u in 0..t, Real.exp (a * u) + Real.exp (-a * u)) =
      (Real.exp (a * t) - Real.exp (-a * t)) / a := by
  have hi (c : ℝ) : IntervalIntegrable (fun u : ℝ => Real.exp (c * u))
      MeasureTheory.volume 0 t := (by fun_prop : Continuous _).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add (hi a) (hi (-a)), exp_integral 0 t a ha,
    exp_integral 0 t (-a) (neg_ne_zero.mpr ha)]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ha]
  <;> ring

#print axioms exp_pair_integral

end LeanLab.Zhao2025.Task56
