/-
P0042 pages 428 and 432: reduce its ratio bound to the maximum bound and known kernel prefixes.
Uses the numerical logarithm certificate machinery in GvLtR1989.Base.
The full-range conclusion is CONDITIONAL only on the full maximum bound.
The low range uses the existing kernel theorem gvltr_ratio_upTo2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.CitedInputs
import LeanLab.GvLtR1989.Chain2
import LeanLab.Verifications.Top50.MinGB1e9

namespace LeanLab.Verifications.RatioReductionTask72

open LeanLab.GvLtR1989 CitedInputs

/-- A certified lower bound for log at the start of the high range. -/
theorem log_1e9_lower : (20.7 : ℝ) ≤ Real.log (10 ^ 9 : ℕ) := by
  have h := le_log_of (x := ((10 ^ 9 : ℕ) : ℝ)) 20 (f := (0.7 : ℝ))
    (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  norm_num at h ⊢
  exact h

/-- A certified lower bound for the iterated logarithm in the high range. -/
theorem log_207_lower : (3 : ℝ) ≤ Real.log 20.7 := by
  have h := le_log_of (x := (20.7 : ℝ)) 3 (f := (0 : ℝ))
    (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  norm_num at h ⊢
  exact h

/-- A certified lower bound for log at the start of the middle range. -/
theorem log_300m_lower : (19.5 : ℝ) ≤ Real.log (300000000 : ℕ) := by
  have h := le_log_of (x := ((300000000 : ℕ) : ℝ)) 19 (f := (0.5 : ℝ))
    (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  norm_num at h ⊢
  exact h

/-- A certified lower bound for the iterated logarithm in the middle range. -/
theorem log_195_lower : (2.95 : ℝ) ≤ Real.log 19.5 := by
  have h := le_log_of (x := (19.5 : ℝ)) 2 (f := (0.95 : ℝ))
    (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  norm_num at h ⊢
  exact h

/-- CONDITIONAL on the full P0042 maximum bound. It supplies the ratio above 1e9. -/
theorem ratio_tail_of_max (hmax : P0042MinimalBound) :
    ∀ n : ℕ, Even n → 10 ^ 9 ≤ n → n ≤ 2 * 10 ^ 10 →
      (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) := by
  apply ratio_of_bound (q := 2029) (r := 20.7) (s := 3)
    (by norm_num) (by norm_num) log_1e9_lower log_207_lower (by norm_num) (by norm_num)
  intro n he hlo hhi
  exact hmax n he (by omega) hhi

/-- The existing kernel bound supplies the middle ratio range with no cited input. -/
theorem ratio_middle_of_small :
    ∀ n : ℕ, Even n → 300000000 ≤ n → n ≤ 10 ^ 9 →
      (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) := by
  apply ratio_of_bound (q := 1789) (r := 19.5) (s := 2.95)
    (by norm_num) (by norm_num) log_300m_lower log_195_lower (by norm_num) (by norm_num)
  intro n he hlo hhi
  exact Top50.Bits.minGB_le_1789_upTo_1e9 n he (by omega) hhi

/-- CONDITIONAL only on the full maximum. Both ratio prefixes are kernel proved. -/
theorem ratio_of_max_and_prefixes (hmax : P0042MinimalBound) : P0042RatioBound := by
  intro n he h6 htop
  by_cases hlowN : n ≤ 300000000
  · exact gvltr_ratio_upTo2 n he h6 (by omega)
  · by_cases hmidN : n ≤ 10 ^ 9
    · exact ratio_middle_of_small n he (by omega) hmidN
    · exact ratio_tail_of_max hmax n he (by omega) htop

end LeanLab.Verifications.RatioReductionTask72
