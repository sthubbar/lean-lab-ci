import LeanLab.RieselVaughan1983.Lemma15
import LeanLab.Common.ThetaWindowDusart
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Chebyshev MeasureTheory Set

namespace LeanLab.RieselVaughan1983

/-- LEAF. Page 56, (4.3): |θ(x) - x| < 0.000154 x / log x for log x ≥ 3000. -/
theorem theta_bound_4_3 (x : ℝ) (hx : 3000 ≤ Real.log x) :
    |θ x - x| < 154 / 1000000 * x / Real.log x := by
  sorry

/-- LEAF. Page 56, (4.4): |θ(x) - x| < 0.00822 x / log x for 22 ≤ log x ≤ 5000. -/
theorem theta_bound_4_4 (x : ℝ) (hx1 : 22 ≤ Real.log x) (hx2 : Real.log x ≤ 5000) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  sorry

/-- LEAF. Page 57, combined bound: |θ(x) - x| < 0.00822 x / log x for log x ≥ 22. -/
theorem theta_bound_combined (x : ℝ) (hx0: 0 < x) (hx : 22 ≤ Real.log x) :
    |θ x - x| < 822 / 100000 * x / Real.log x := by
  by_cases hx3000 : 3000 ≤ Real.log x
  · have h1 := theta_bound_4_3 x hx3000
    have h2 : (154 : ℝ) / 1000000 ≤ (822 : ℝ) / 100000 := by norm_num
    have h22 : (0 : ℝ) ≤ 22 := by norm_num
    have h3 : 0 ≤ x / Real.log x := div_nonneg hx0.le (h22.trans hx)
    calc |θ x - x| < 154 / 1000000 * x / Real.log x := h1
      _ = 154 / 1000000 * (x / Real.log x) := by ring
      _ ≤ 822 / 100000 * (x / Real.log x) := mul_le_mul_of_nonneg_right h2 h3
      _ = 822 / 100000 * x / Real.log x := by ring
  · push Not at hx3000
    have hx3000_le : Real.log x ≤ 5000 := hx3000.le.trans (by norm_num)
    exact theta_bound_4_4 x hx hx3000_le

/-- LEAF. Page 57, integral bound for prime counting. -/
theorem lemma6ii_integral (x : ℝ) (hx0 : 0 < x) (hx300 : 300 ≤ Real.log x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / Real.log x + 10151 / 10000 * x / Real.log x ^ 2 := by
  sorry

/-- The exact cited statement of Lemma 6 (ii). -/
theorem lemma6ii_decomposed : Lemma6ii := by
  intro x hx0 hx300
  exact lemma6ii_integral x hx0 hx300

end LeanLab.RieselVaughan1983
