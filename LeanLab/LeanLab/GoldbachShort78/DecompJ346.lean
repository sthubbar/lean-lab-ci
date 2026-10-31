import LeanLab.GoldbachShort78.BHPTiling

open LeanLab.GoldbachShort78

namespace LeanLab.GoldbachShort78

/-- LEAF p. 562 display
The main printed count inequality of BHP 2001. -/
theorem leaf_bhp_1 :
  ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
      ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) := sorry

/-- Assembly of the final printed display from the leaf. -/
theorem bhp_printed_count_assembly : BHPPrintedCount := by
  exact leaf_bhp_1

end LeanLab.GoldbachShort78
