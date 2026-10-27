/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Finite inverse twin products lie between 1 and their positive infinite limit.
-/
import LeanLab.Routes.Task59InverseTwin

namespace LeanLab.Routes.Task59

open Finset

/-- Uniform bounds for any finite product over odd primes. -/
theorem finite_inverse_twin_bounds (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    1 ≤ (∏ p ∈ s, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) ∧
      (∏ p ∈ s, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
        LeanLab.Routes.U1451.twinProd⁻¹ := by
  classical
  let g : ℕ → ℝ := fun p => ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))
  have hg (p : ℝ) (hp : 2 < p) : 1 ≤ (p - 1) ^ 2 / (p * (p - 2)) := by
    have hd : 0 < p * (p - 2) := mul_pos (by linarith) (by linarith)
    apply (one_le_div hd).mpr
    nlinarith
  change 1 ≤ (∏ p ∈ s, g p) ∧ (∏ p ∈ s, g p) ≤ _
  constructor
  · exact one_le_prod₀ (fun p hp => hg p (by exact_mod_cast (hs p hp).2))
  · have hh : (∏ p ∈ s.subtype (fun p : ℕ => p.Prime ∧ 2 < p), g p.1) ≤
        LeanLab.Routes.U1451.twinProd⁻¹ := by
      apply prod_le_hasProd_of_nonneg _ _ inverse_twin_hasProd
      · intro p _
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
          (hg p.1 (by exact_mod_cast p.property.2))
      · intro p _
        exact hg p.1 (by exact_mod_cast p.property.2)
    rw [prod_subtype_of_mem g hs] at hh
    exact hh

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.finite_inverse_twin_bounds
