/-
Incomplete three-square coefficient periods from page 15 after display 51.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403a

namespace LeanLab.KumchevLiu2007.Task403b

open Real Complex Task129b Task129c Task403a
open scoped BigOperators

/-- Page 15 second display. A partial three-square coefficient period is bounded
by twice the absolute sum over a full joint period. -/
theorem A3_interval_bound {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, A3 n q * A3 n r‖ ≤
      2 * ∑ n ∈ Finset.range (q * r), ‖A3 n q * A3 n r‖ := by
  have hq' : Function.Periodic (fun n => A3 n q) (q * r) := by
    simpa [Nat.mul_comm] using (A3_periodic q).nat_mul r
  have hr' : Function.Periodic (fun n => A3 n r) (q * r) := by
    simpa using (A3_periodic r).nat_mul q
  exact periodic_zero_mean_interval _ (Nat.mul_pos hq hr) (hq'.mul hr')
    (A3_orthogonal q r hqr) a b

/-- Page 15 second display. Reality gives the conjugated partial period estimate. -/
theorem A3_conjugate_interval_bound {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, A3 n q * (starRingEnd ℂ) (A3 n r)‖ ≤
      2 * ∑ n ∈ Finset.range (q * r),
        ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖ := by
  simpa only [Task342h.A3_conj] using A3_interval_bound hq hr hqr a b

end LeanLab.KumchevLiu2007.Task403b
