import LeanLab.Pintz2021.Truncation168
import LeanLab.Pintz2021.LeafAudit168

/-!
P0054 page 8 display 2.22 with the actual finite restrictions.
These assembly theorems are CONDITIONAL ON the major arc bound and discarded term bound.
They do not assert either analytic input or the false sealed Theorem1_220.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Assembly168

open State1581 DecompJ281 Truncation168 Finset

attribute [local instance] Classical.propDecidable

/-- CONDITIONAL ON the two supplied analytic bounds, the errors add exactly. -/
theorem truncated_formula_of_bounds (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U H c C Ctail : ℝ) (m : ℕ)
    (hmajor : ‖R1majPrime ε X P m - mainTermPrime (E : Set ExcPair) Sg ε X m‖ ≤
      C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)))
    (htail : (∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, ‖pairTerm Sg ε X m p‖) ≤
      Ctail * (Sing m * X * Real.log U / Real.sqrt U)) :
    ‖R1majPrime ε X P m - truncatedPrime E Sg ε X P U m‖ ≤
      C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) +
        Ctail * (Sing m * X * Real.log U / Real.sqrt U) := by
  calc
    _ ≤ ‖R1majPrime ε X P m - mainTermPrime (E : Set ExcPair) Sg ε X m‖ +
        ‖mainTermPrime (E : Set ExcPair) Sg ε X m - truncatedPrime E Sg ε X P U m‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) +
        ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, ‖pairTerm Sg ε X m p‖ :=
      add_le_add hmajor (norm_truncation_error_le E Sg ε X P U m)
    _ ≤ _ := add_le_add le_rfl htail

/-- CONDITIONAL ON those analytic bounds, a common constant is valid at nonnegative scale. -/
theorem truncated_formula_common_constant (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U H c C Ctail : ℝ) (m : ℕ)
    (hX : 0 ≤ X) (hU : 1 ≤ U)
    (hmajor : ‖R1majPrime ε X P m - mainTermPrime (E : Set ExcPair) Sg ε X m‖ ≤
      C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)))
    (htail : (∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, ‖pairTerm Sg ε X m p‖) ≤
      Ctail * (Sing m * X * Real.log U / Real.sqrt U)) :
    ‖R1majPrime ε X P m - truncatedPrime E Sg ε X P U m‖ ≤
      max C Ctail * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε) +
        Sing m * X * Real.log U / Real.sqrt U) := by
  have hS : 0 ≤ Sing m := (Applications.Sing_pos m).le
  have hlog : 0 ≤ Real.log U := Real.log_nonneg hU
  have hfirst : 0 ≤ Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε) := by positivity
  have hsecond : 0 ≤ Sing m * X * Real.log U / Real.sqrt U := by positivity
  apply (truncated_formula_of_bounds E Sg ε X P U H c C Ctail m hmajor htail).trans
  calc
    _ ≤ max C Ctail * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε)) +
        max C Ctail * (Sing m * X * Real.log U / Real.sqrt U) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hfirst)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hsecond)
    _ = _ := by ring

/-- A nonempty finite model realizes both assembly hypotheses with zero error. -/
theorem bounds_instance :
    ∃ E : Finset ExcPair, E.Nonempty ∧ ∃ Sg : ExcPair → ExcPair → ℕ → ℂ,
      ‖R1majPrime 1 3 1 1 - mainTermPrime (E : Set ExcPair) Sg 1 3 1‖ = 0 ∧
        (∑ p ∈ (E ×ˢ E) \ retainedPairs E 1 2 1, ‖pairTerm Sg 1 3 1 p‖) = 0 := by
  refine ⟨{pole}, by simp, fun _ _ _ => R1majPrime 1 3 1 1, ?_, ?_⟩
  · rw [mainTermPrime_eq_sum]
    simp [pairTerm, mult_pole, Asign_pole, X1, LeafAudit168.kernel_instance,
      show pole.ρ = 1 from rfl]
  · have hr : retainedPairs ({pole} : Finset ExcPair) 1 2 1 =
        ({pole} : Finset ExcPair) ×ˢ {pole} := by
      apply Subset.antisymm (filter_subset _ _) ?_
      rintro ⟨z, w⟩ hp
      simp only [mem_product, mem_singleton] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact pole_pair_retained (by simp) (by norm_num) (by norm_num) 1
    rw [hr, sdiff_self]
    simp

end LeanLab.Pintz2021.Assembly168

#print axioms LeanLab.Pintz2021.Assembly168.truncated_formula_of_bounds
#print axioms LeanLab.Pintz2021.Assembly168.truncated_formula_common_constant

#print axioms LeanLab.Pintz2021.Assembly168.bounds_instance
