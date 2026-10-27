import LeanLab.OeSHP2014.Task74Moments
import LeanLab.OeSHP2014.Task74Moment2
import LeanLab.OeSHP2014.Task74Moment3
import LeanLab.OeSHP2014.Task74Moment4

/-! Cross column checks of all printed normalized moments in Table 12, page 2056.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- The printed columns for moments two, three and four, paired by cutoff. -/
def momentTriples : List (ℚ × ℚ × ℚ) :=
  (momentRows2.zip (momentRows3.zip momentRows4)).map
    (fun r => (r.1.2, r.2.1.2, r.2.2.2))

/-- Every printed triple passes both necessary moment inequalities. -/
theorem table12_cross_moments : ∀ r ∈ momentTriples,
    2 * r.1 ^ 2 ≤ 3 * r.2.1 ∧ 3 * r.2.1 ^ 2 ≤ 4 * r.1 * r.2.2 := by
  norm_num [momentTriples, momentRows2, momentRows3, momentRows4, List.zip, List.zipWith]

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table12_cross_moments
