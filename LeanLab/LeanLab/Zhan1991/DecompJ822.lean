import LeanLab.Zhan1991.Fourier110

/-!
Decomposition of minor_reduction110.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open MeasureTheory



/-- LEAF. Page 269, window card bound. The cardinality of the prime window is bounded by its length. -/
theorem win_card110 (N : ℕ) (U : ℝ) :
    ((Win N U).card : ℝ) ≤ 3 * U := by
  sorry

/-- LEAF. The integral of minor arcs is bounded by sup times L2. -/
theorem minor_integral_bound110 (N : ℕ) (U d : ℝ) (K : ℝ)
    (h_sup : ∀ α ∈ minorArcs110 N U d, ‖primeSum110 N U α‖ ≤ K * U * Real.log N ^ (-4 : ℝ)) :
    |minorTerm110 N U d| ≤
      (K * U * Real.log N ^ (-4 : ℝ)) *
      (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := by
  sorry



end
end LeanLab.Zhan1991
