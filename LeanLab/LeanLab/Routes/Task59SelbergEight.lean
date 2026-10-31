/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The weak Selberg upper bound requested by the U1436 next action.
-/
import LeanLab.Routes.Task59SelbergAsymptotic
import LeanLab.Routes.Task59TotientProduct

namespace LeanLab.Routes.Task59

open Finset Real Filter Topology LeanLab.Routes.U1431

/-- The eventual coefficient 8 upper bound with the odd prime local factors. -/
theorem eventually_rG_le_eight_product (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 ∣ N →
      (rG N : ℝ) ≤ (8 + ε) *
        (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ) / ((p : ℝ) - 1)) *
          (N : ℝ) / log N ^ 2 := by
  filter_upwards [eventually_rG_le_four_totient (ε / 2) (by positivity),
    eventually_ge_atTop 2] with N h hN
  intro hev
  have hh := h hev
  rw [totient_ratio_even_eq_two_prod hN hev] at hh
  convert hh using 1 <;> ring

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.eventually_rG_le_eight_product
