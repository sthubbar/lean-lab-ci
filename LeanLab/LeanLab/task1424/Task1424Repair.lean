/-
Repair record for the rejected branch free-nv-glm5/task1424, which ran on
DtRS1998/SPLIT_leaf_quarter_first_250.lean.

The branch replaced the sorry on `leaf_eighth_first_250` there with a proof
sketch, so that existing file went from 4 sorries to 5 and the gate rejected
the branch.  The sketch does not build: its last step runs `decide` on a goal
that still contains the free index j, and its own check receipt
(build/FREE-nv-glm5-task1424-CHECK.txt, carried into this folder) records
`lake build LeanLab.DtRS1998.SPLIT_leaf_quarter_first_250 exit 1`.

The repair therefore restores that file to its main blob, byte for byte, so
the statement and its sorry are exactly as on main and no existing file gains
a sorry.  Nothing is claimed about `leaf_eighth_first_250` here.

What the branch did contribute is a concrete candidate list,
[10 ^ 250 - 677, 10 ^ 250 - 983], and the theorem below records, in the
kernel, why that list cannot be the one the leaf asks for: at the second index
of the eighth the two differences it would have to make prime are 679 and 985,
and neither is prime.

The arithmetic is closed, so the theorem carries no hypothesis and cannot be
vacuous.  Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Task1424

/-- The branch's list fails at the index j = 1 of the first eighth: the two
differences 10 ^ 250 + 2 * 1 - q it would have to make prime are 679 = 7 * 97
and 985 = 5 * 197, so neither entry of the list covers that index. -/
theorem branch_list_uncovered_at_one :
    (10 ^ 250 + 2 * 1 - (10 ^ 250 - 677)) = 679 ∧
      (10 ^ 250 + 2 * 1 - (10 ^ 250 - 983)) = 985 ∧
        ¬ (679 : ℕ).Prime ∧ ¬ (985 : ℕ).Prime := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Task1424
