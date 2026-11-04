import LeanLab.ChirreHagen2025.Decomp272a

/-!
P0075 page 6, the first display obtained from equation 2.11.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp272b

open Decomp272a

/-- LEAF. P0075 page 6, first display, differentiating equation 2.11.
HasSum supplies the differentiated series identity and its convergence. -/
theorem differentiated_laurent_series (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * laurentCoeff (n + 1) *
      ((t : ℂ) * Complex.I) ^ n)
      (deriv riemannZeta (1 + t * Complex.I) - 1 / (t : ℂ) ^ 2) := by
  sorry

/-- LEAF. P0075 page 6, first display, the two geometric majorants.
This is a series comparison for arbitrary complex coefficients. The coefficient
bounds are reused from page 5, and no zeta estimate is assumed here. -/
theorem differentiated_laurent_majorant (a : ℕ → ℂ) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (htop : t ≤ 1 / 2)
    (hsum : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) *
      ((t : ℂ) * Complex.I) ^ n) z)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤
      (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) :
    ‖z‖ ≤ 4 / (2 * Real.pi - 1) + 4 / (4 * Real.pi ^ 2 - 1) := by
  sorry

/-- LEAF. P0075 page 6, first display, last inequality.
This numerical step uses only a rational lower bound for pi. -/
theorem derivative_majorant_numeric :
    (4 : ℝ) / (2 * Real.pi - 1) + 4 / (4 * Real.pi ^ 2 - 1) ≤ 0.862 := by
  have hp : (3.141592 : ℝ) ≤ Real.pi := Real.pi_gt_d6.le
  calc
    (4 : ℝ) / (2 * Real.pi - 1) + 4 / (4 * Real.pi ^ 2 - 1)
        ≤ 4 / (2 * 3.141592 - 1) + 4 / (4 * 3.141592 ^ 2 - 1) := by
          gcongr
    _ ≤ 0.862 := by norm_num

/-- P0075 page 6. The exact statement of Decomp122.deriv_remainder.
CONDITIONAL ON the two new series leaves and the page 5 coefficient leaf. -/
theorem deriv_remainder (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    ‖deriv riemannZeta (1 + t * Complex.I) - 1 / (t : ℂ) ^ 2‖ ≤ 0.862 := by
  exact (differentiated_laurent_majorant laurentCoeff _ t ht htop
    (differentiated_laurent_series t ht htop)
    laurent_coefficient_bounds.2).trans derivative_majorant_numeric

end LeanLab.ChirreHagen2025.Decomp272b
