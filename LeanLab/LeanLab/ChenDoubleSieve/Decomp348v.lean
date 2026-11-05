import LeanLab.ChenDoubleSieve.Decomp348n
import LeanLab.ChenDoubleSieve.Decomp348l
import LeanLab.ChenDoubleSieve.Decomp348j

/-!
Concrete nonempty witnesses for the lower sieve supply domains.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
These are hypothesis instances, not finite substitutes for asymptotic estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Set
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- Exact and enclosing power cutoffs for a nonempty pair domain instance. -/
theorem pair_instance_cutoffs :
    (((281474976710656 : ℕ) : ℝ) ^ kappa1) = 16 ∧
      (32 : ℝ) ≤ ((281474976710656 : ℕ) : ℝ) ^ kappa2 ∧
      (((281474976710656 : ℕ) : ℝ) ^ kappa2) ≤ 64 ∧
      (((281474976710656 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) = 65536 := by
  have he (r : ℝ) : (((281474976710656 : ℕ) : ℝ) ^ r) = (2 : ℝ) ^ (48 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    norm_num [kappa1]
  · rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (5 : ℝ) ≤ 48 * kappa2)
    norm_num at h
    exact h
  · rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : 48 * kappa2 ≤ (6 : ℝ))
    norm_num at h
    exact h
  · rw [he]
    norm_num

/-- The standard function assumptions used by all three supplies have a clean common witness. -/
theorem function_hypotheses_instance : ∃ F f ω : ℝ → ℝ,
    Wu04Functional.IsLinearSieve F f ∧ Wu04Functional.IsBuchstab ω :=
  Task275.standard_functions

end LeanLab.ChenDoubleSieve.Task348
