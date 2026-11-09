/- AI wrote this Lean code for CODEX task327. Goldbach is open.
Concrete domains for the supply leaves. Journal pp. 1218 and 1219.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp327a
import LeanLab.BS2022GRH.SieveAllLevels1611

namespace LeanLab.BS2022GRH.Instances327
open Real Finset Classical ChenThresholdGRH Decomp148f Decomp327a
noncomputable section

/-- The actual selected product premise has a nonzero prime density instance.
Reuse the existing all-level instance with epsilon one over 8349.
Journal p. 1218 display 2. -/
theorem selected_product_instance :
    ∀ (n : ℕ) (u : ℝ), 1 < u → u < 10 →
      ∏ p ∈ (range ⌈(10 : ℝ)⌉₊).filter
        (fun p => p ∈ ({5} : Set ℕ) ∧ p ∉ (∅ : Finset ℕ) ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < 10),
        (1 - (1 / 8350 : ℝ))⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log 10 / log u) := by
  intro n u hu huz
  have h := SieveAllLevels1611.allLevelsPremise_instance
    (ε := (1 / 8349 : ℝ)) (z := (10 : ℝ)) (by norm_num)
  have he : (1 / 8349 : ℝ) / (1 + 1 / 8349) = 1 / 8350 := by norm_num
  convert h n u 10 hu huz le_rfl using 1 <;> norm_num [he]

/-- A prime with density one over 8350 satisfies the prime and density guards.
The upper and lower levels ten and one hundred are both admissible.
Journal p. 1218 Theorem 4. -/
theorem selected_prime_domain :
    (∀ p ∈ ({5} : Set ℕ), p.Prime) ∧
    (∀ p ∈ ({5} : Set ℕ), 0 ≤ (1 / 8350 : ℝ) ∧ (1 / 8350 : ℝ) < 1) ∧
    (2 : ℝ) ≤ 10 ∧ (10 : ℝ) ≤ 10 ∧ (10 : ℝ) ^ 2 ≤ 100 := by
  norm_num

/-- The logarithmic sieve parameters at those levels are one and two.
Journal p. 1219 definition of s. -/
theorem selected_parameters :
    log (10 : ℝ) / log 10 = 1 ∧ log (100 : ℝ) / log 10 = 2 := by
  have hlog : log (10 : ℝ) ≠ 0 := ne_of_gt (log_pos (by norm_num))
  constructor
  · exact div_self hlog
  · rw [show (100 : ℝ) = 10 ^ 2 by norm_num, log_pow]
    field_simp
    norm_num

/-- The nonzero cube boundary also lies in both selected sieve ranges.
Journal pp. 1218 and 1219, with z equal to ten and D equal to 125. -/
theorem cube_boundary_parameters :
    (2 : ℝ) ≤ log 125 / log 10 ∧ log 125 / log 10 ≤ 3 := by
  have hlog : 0 < log (10 : ℝ) := log_pos (by norm_num)
  have hlo := log_le_log (show (0 : ℝ) < 100 by norm_num)
    (show (100 : ℝ) ≤ 125 by norm_num)
  have hhi := log_le_log (show (0 : ℝ) < 125 by norm_num)
    (show (125 : ℝ) ≤ 1000 by norm_num)
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, log_pow] at hlo
  rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, log_pow] at hhi
  norm_num at hlo hhi
  constructor
  · exact (le_div_iff₀ hlog).2 (by linarith)
  · exact (div_le_iff₀ hlog).2 (by linarith)

/-- The first stopping term can be nonzero at an exact cube boundary.
BJS p. 10 display 28. The density is the preceding admissible positive one. -/
theorem stopping_nonzero_instance :
    stoppingTerm {5} 125 (fun _ => (1 / 8350 : ℝ)) 1 = 1 / 8350 := by
  rw [stoppingTerm_one]
  norm_num [Finset.filter_singleton]

/-- The first scalar delay term has the paper's explicit initial values.
BJS p. 6 display 15. -/
theorem delay_initial_instances : delayTerm 1 2 = 1 / 2 ∧ delayTerm 1 3 = 0 := by
  norm_num [delayTerm]

#print axioms selected_product_instance
#print axioms selected_prime_domain
#print axioms selected_parameters
#print axioms cube_boundary_parameters
#print axioms stopping_nonzero_instance
#print axioms delay_initial_instances

end
end LeanLab.BS2022GRH.Instances327
