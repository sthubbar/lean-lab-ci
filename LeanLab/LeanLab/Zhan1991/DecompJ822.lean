import LeanLab.Zhan1991.Fourier110
import LeanLab.Zhan1991.Decomp110

/-!
Decomposition of minor_reduction110.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open MeasureTheory



/-- Page 269, window card bound. The cardinality of the prime window is bounded by its length.
Repaired 2026-11-02, U-1601: the unrestricted form fails at N = 6, U = 0, Audit1601.not_win_card_nonneg;
the paper's U is large. -/
theorem win_card110 (N : ℕ) (U : ℝ) (hU : 1 ≤ U) :
    ((Win N U).card : ℝ) ≤ 3 * U :=
  win_card_three226 N U hU

/-- The integral of minor arcs is bounded by sup times L2. Repaired 2026-11-02, U-1601: the bound
must be nonnegative; K = -1, N = 9, U = d = 1 refutes the unrestricted form, task 226. -/
theorem minor_integral_bound110 (N : ℕ) (U d : ℝ) (K : ℝ)
    (hM : 0 ≤ K * U * Real.log N ^ (-4 : ℝ))
    (h_sup : ∀ α ∈ minorArcs110 N U d, ‖primeSum110 N U α‖ ≤ K * U * Real.log N ^ (-4 : ℝ)) :
    |minorTerm110 N U d| ≤
      (K * U * Real.log N ^ (-4 : ℝ)) *
      (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := by
  have e : (T N U : ℝ) - majorTerm110 N U d = minorTerm110 N U d := minor_identity226 N U d
  rw [primeSum_L2_110, ← e]
  exact minor_difference_bound226 N U d _ hM h_sup



end
end LeanLab.Zhan1991
