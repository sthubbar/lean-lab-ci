/-
P0076 Theorems 1.1 through 1.4, with their original sealed statements.
Each assembly is CONDITIONAL ON the named unresolved inputs in MainInputs.lean.
The elementary reductions have separate clean axiom logs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

/-- Theorem 1.1, CONDITIONAL ON the four named binary analytic inputs. -/
theorem theorem_1_1 : Theorem11 :=
  theorem11_after_prop21 paper_smooth_cutoff_input paper_weighted_prime_input
    paper_half_interval_input (prop33_of_cross paper_cross_scale_restriction_input)

/-- Theorem 1.2, CONDITIONAL ON ternary transference and the prime distribution inputs. -/
theorem theorem_1_2 : Theorem12 :=
  theorem12_conditional paper_ternary_transference_input paper_weighted_prime_input
    paper_cross_scale_restriction_input

/-- Theorem 1.3, CONDITIONAL ON the Section 4 modular progression input. -/
theorem theorem_1_3 : Theorem13 := by
  intro A hA hδ
  exact infinitelyMany3AP_of_middle_thirds (paper_dense_modular_progressions_input A hA hδ)

/-- Theorem 1.4, CONDITIONAL ON the Section 11 dyadic prime approximation input. -/
theorem theorem_1_4 : Theorem14 :=
  theorem14_of_dyadic_input paper_dyadic_approximation_input

#print axioms theorem_1_1
#print axioms theorem_1_2
#print axioms theorem_1_3
#print axioms theorem_1_4

end LeanLab.Teravainen2016
