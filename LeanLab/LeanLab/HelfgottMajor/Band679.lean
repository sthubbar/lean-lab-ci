import LeanLab.HelfgottMajor.ZeroCount1623

/-!
The endpoint envelope from book page 431 display 16.21 exceeds three.
It cannot by itself certify a cardinal bound of one in DecompF1607.
This is an arithmetic limitation of this proof route, not a counterexample to the targets.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623

/-- Book page 431 display 16.21 at the top of the short band.
The main term vanishes, and the upper envelope is greater than three. -/
theorem book_band_top_envelope_gt_three_task679 (q : ℕ) [NeZero q] :
    3 < bookMain q (2 * Real.pi * Real.exp 1 / (q : ℝ)) +
      bookError q (2 * Real.pi * Real.exp 1 / (q : ℝ)) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hp : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
  have hc : (q : ℝ) * (2 * Real.pi * Real.exp 1 / (q : ℝ)) =
      2 * Real.pi * Real.exp 1 := by field_simp
  rw [bookMain, bookError, hc, div_self hp, Real.log_one, mul_zero, zero_add]
  have he := Real.add_one_le_exp (1 : ℝ)
  have hl : 0 ≤ Real.log (2 * Real.pi * Real.exp 1) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.book_band_top_envelope_gt_three_task679
