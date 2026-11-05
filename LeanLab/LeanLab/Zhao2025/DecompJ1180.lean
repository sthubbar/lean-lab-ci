import Mathlib
import LeanLab.Zhao2025.PaperTheorem14
import LeanLab.Zhao2025.DecompJ1123

namespace LeanLab.Zhao2025.Task1180

open LeanLab.Zhao2025.Task56

/-- LEAF: Core analytic bound without the division by log. -/
theorem maynard_2013_core (theta : ℝ) (hth : 5 ≤ theta) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 2 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) * Real.log ((q : ℝ) ^ theta) ≤
        2 * (q : ℝ) ^ theta / (Nat.totient q : ℝ) := by
  sorry

/-- LEAF: Rearrangement of the bound. -/
theorem maynard_rearrange (q : ℕ) (hq : 2 ≤ q) (theta : ℝ) (hth : 5 ≤ theta) (a : ℕ)
    (h_bound : (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) * Real.log ((q : ℝ) ^ theta) ≤
        2 * (q : ℝ) ^ theta / (Nat.totient q : ℝ)) :
    (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
      2 * (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega)
  have ht : 0 < theta := by linarith
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega)
  have hlog : 0 < Real.log ((q : ℝ) ^ theta) := by
    apply Real.log_pos
    exact Real.one_lt_rpow hq1 ht
  have hdiv : (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) * Real.log ((q : ℝ) ^ theta) / Real.log ((q : ℝ) ^ theta) ≤
    (2 * (q : ℝ) ^ theta / (Nat.totient q : ℝ)) / Real.log ((q : ℝ) ^ theta) := div_le_div_of_nonneg_right h_bound (le_of_lt hlog)
  have hcancel : (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) * Real.log ((q : ℝ) ^ theta) / Real.log ((q : ℝ) ^ theta) = (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) := mul_div_cancel_right₀ _ (ne_of_gt hlog)
  have hrhs : (2 * (q : ℝ) ^ theta / (Nat.totient q : ℝ)) / Real.log ((q : ℝ) ^ theta) =
    2 * (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by ring
  rwa [hcancel, hrhs] at hdiv

theorem maynard_2013_bound (theta : ℝ) (hth : 5 ≤ theta) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        2 * (q : ℝ) ^ theta / ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  obtain ⟨Q, hQ⟩ := maynard_2013_core theta hth
  use max Q 2
  intro q hq hq1 a ha1 haq hcop
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
  have hcore := hQ q ((le_max_left Q 2).trans hq) hq2 a ha1 haq hcop
  exact maynard_rearrange q hq2 theta hth a hcore

end LeanLab.Zhao2025.Task1180
