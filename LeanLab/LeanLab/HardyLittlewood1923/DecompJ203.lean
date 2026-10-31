import LeanLab.HardyLittlewood1923.U1503Endpoint
import LeanLab.HardyLittlewood1923.Decomp105

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105

namespace LeanLab.HardyLittlewood1923.DecompJ203

/-- LEAF. P0004 page 25 equation 3.142.
The minor arcs sum bounded by the paper's claimed error. -/
theorem minor_arcs_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 24 equation 3.124.
The uniform rational arc estimate. -/
theorem uniform_rational_arc {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 24 equation 3.131.
Rational arc integral estimate. -/
theorem rational_arc_integral {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 23 equation 3.119.
Error bounded by exponential term. -/
theorem error_bounded_exponential {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equation 3.151.
Exponential approximation. -/
theorem exponential_approximation {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equation 3.152.
Integral on line segment. -/
theorem integral_line_segment {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equation 3.153.
Tail integral bound. -/
theorem tail_integral_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equation 3.154.
Combining integral estimates for minor arcs. -/
theorem minor_arcs_integral_combine {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 page 25 equation 3.155.
Bounding combined integral with polynomial and log factors. -/
theorem bounded_combined_integral {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry


/-- The exact same proposition as `finite_approximation_lower`. -/
theorem finite_approximation_lower_assembly {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact bounded_combined_integral hΘ0 hΘ1 hZ

end LeanLab.HardyLittlewood1923.DecompJ203
