/-
P0017 p. 1748 Section 6, the logarithmic consequence for even arguments.
The least Goldbach prime is the lab's existing minGB function.
The conjectured bound and positivity are explicit inputs.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Richstein2001.LogQuotient116
import LeanLab.Richstein2001.Table1
open Filter
open scoped Topology
namespace LeanLab.Richstein2001
open LeanLab.Verifications
/-- CONDITIONAL ON the conjectured growth bound and existence of a smaller prime.
P0017 p. 1748 Section 6, last sentence, with even argument 2n. -/
theorem even_minGB_quotient116 (C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, 2 ≤ minGB (2 * n) ∧
      (minGB (2 * n) : ℝ) ≤ C * Real.log (2 * (n : ℝ)) ^ 2 *
        Real.log (Real.log (2 * (n : ℝ)))) :
    Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) /
      Real.log (minGB (2 * n) : ℝ) ^ 2) atTop atTop := by
  apply quotient_tendsto116 (fun n : ℕ => 2 * (n : ℝ))
    (fun n => (minGB (2 * n) : ℝ))
    (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop) C hC
  filter_upwards [h] with n hn
  exact ⟨by exact_mod_cast hn.1, hn.2⟩
end LeanLab.Richstein2001
