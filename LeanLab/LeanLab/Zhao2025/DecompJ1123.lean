import Mathlib
import LeanLab.Zhao2025.PaperTheorem14

namespace LeanLab.Zhao2025.Task1123

open LeanLab.Zhao2025.Task56

/-- LEAF: The deep analytic bound from Maynard 2013 for exponent at least 5.

REPAIRED (U-1619): constant `2 + epsilon` and the modulus threshold after `epsilon`,
which is Zhao (1.16); the earlier constant `2` form asked one `Q` to serve every `epsilon`. -/
theorem maynard_2013_bound (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ) (heps : 0 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  sorry

/-- LEAF: Nonnegativity of the scaling term. -/
theorem scaling_term_nonneg (q : ℕ) (hq : 2 ≤ q) (theta : ℝ) (hth : 5 ≤ theta) :
  0 ≤ (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by linarith : 0 < q)
  have htot : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by linarith)
  have hqpow : (0 : ℝ) < (q : ℝ) ^ theta := Real.rpow_pos_of_pos hq0 theta
  have hlog : (0 : ℝ) < Real.log ((q : ℝ) ^ theta) := by
    apply Real.log_pos
    have h1 : (1 : ℝ) < q := by exact_mod_cast (by linarith : 1 < q)
    have ht : 0 < theta := by linarith
    exact Real.one_lt_rpow h1 ht
  exact div_nonneg hqpow.le (mul_nonneg htot.le hlog.le)

theorem leaf2_low (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ)
    (heps : 0 < epsilon) (hlow : theta ≤ 1 + 2 / epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  have _ := hlow
  exact maynard_2013_bound theta hth epsilon heps

end LeanLab.Zhao2025.Task1123
