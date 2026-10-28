import LeanLab.RieselVaughan1983.Lemma8
import LeanLab.Common.ThetaWindowDusart
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Chebyshev MeasureTheory Set

namespace LeanLab.RieselVaughan1983

/-- LEAF. Page 56, (4.5): θ(x) > x - 0.00862 x / log x for log x >= 22. -/
theorem theta_lower_bound_4_5 (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ Real.log x) :
    x - 862 / 100000 * x / Real.log x < θ x := by
  sorry

/-- LEAF. Page 56, integral bound leading to (4.1) for log x >= 32. -/
theorem lemma6i_integral_32 (x : ℝ) (hx0 : 0 < x) (hx : 32 ≤ Real.log x) :
    x / Real.log x + 9911 / 10000 * x / Real.log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  sorry

/-- LEAF. Page 57, Rosser-Schoenfeld corollary bound for log x between 17 and 35. -/
theorem lemma6i_integral_17_35 (x : ℝ) (hx0 : 0 < x) (hx1 : 17 ≤ Real.log x) (hx2 : Real.log x ≤ 35) :
    x / Real.log x + 9911 / 10000 * x / Real.log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  sorry

/-- The exact cited statement of Lemma 6 (i). -/
theorem lemma6i_decomposed : Lemma6i := by
  intro x hx0 hx17
  by_cases hx32 : 32 ≤ Real.log x
  · exact lemma6i_integral_32 x hx0 hx32
  · push Not at hx32
    exact lemma6i_integral_17_35 x hx0 hx17 (hx32.le.trans (by norm_num))

end LeanLab.RieselVaughan1983
