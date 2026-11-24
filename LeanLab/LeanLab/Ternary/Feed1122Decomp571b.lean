/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
Both open limits of Decomp571b are already reduced elsewhere in the lab:
the first rough term to the prime and composite leaves of Decomp581a,
the ordered triple correction to the cofactor leaves of Decomp581b,
through the sorry free reindexing of Decomp581c.
This file only connects the sealed statements to those existing supplies.
No new leaf is introduced. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp571b
import LeanLab.Ternary.Decomp581a
import LeanLab.Ternary.Decomp581c

namespace LeanLab.Ternary.MMS.Task571
open Finset MeasureTheory

/-- The first rough limit from the existing Decomp581a leaves.
MMS page 11 bottom display, first term.
CONDITIONAL ON Task581.primeMean_limit and Task581.compositeMean_limit. -/
theorem roughReferenceMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |roughReferenceMean x - 4 * buchstabModel 4| ≤ δ := by
  unfold roughReferenceMean
  exact Task581.roughReferenceMean_limit_supply

/-- The ordered triple correction limit from the existing Decomp581b leaves.
MMS page 11 equation 5.1 and bottom display, continued on page 12.
CONDITIONAL ON Task581.cofactorMean_uniform and Task581.cofactorModel_sum_limit. -/
theorem correctionReferenceMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |correctionReferenceMean x - profileIntegral buchstabModel| ≤ δ := by
  unfold correctionReferenceMean
  exact Task581.correctionReferenceMean_limit_supply

end LeanLab.Ternary.MMS.Task571
