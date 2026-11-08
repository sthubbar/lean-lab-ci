import LeanLab.ExceptionalSet.Decomp462f

/-!
P0082 page 356, shape properties of the explicit trapezoid and kernel.
Source: https://doi.org/10.5802/aif.1621
The parity and continuity assertions are printed below display 2.
The value at zero is the auxiliary continuous extension of display 3.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462i

open Real MeasureTheory
open LeanLab.ExceptionalSet
open LeanLab.ExceptionalSet.U1539 (Kfun)
/-- P0082 page 356, displays 2 and 3. The paper kernel is even. -/
theorem Kfun_even (Δ x : ℝ) : Kfun Δ (-x) = Kfun Δ x := by
  simp [Kfun, mul_neg]
/-- P0082 page 356, displays 2 and 3. The continuous kernel value at zero is two minus Delta for nonzero Delta. -/
theorem Kfun_zero (Δ : ℝ) (hΔ : Δ ≠ 0) : Kfun Δ 0 = 2 - Δ := by
  simp only [Kfun, mul_zero, Real.sinc_zero, one_pow, mul_one]
  field_simp
  ring
/-- P0082 page 356, displays 2 and 3. The trapezoid weight is even. -/
theorem weight_even (Δ ξ : ℝ) : KernelTransform264.weight Δ (-ξ) = KernelTransform264.weight Δ ξ := by
  simp [KernelTransform264.weight, neg_div, abs_neg]
/-- P0082 page 356, displays 2 and 3. The trapezoid weight is continuous. -/
theorem weight_continuous (Δ : ℝ) : Continuous (KernelTransform264.weight Δ) := by
  unfold KernelTransform264.weight
  fun_prop

end LeanLab.ExceptionalSet.Decomp462i
