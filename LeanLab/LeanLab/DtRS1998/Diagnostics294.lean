/-
AI wrote this Lean code for CODEX task294.
P0037 Section 5.1 page 211 and Table 1 page 213 give the target range.
These are diagnostics for our incomplete certificate search.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Diagnostics294

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The trial division part divides the candidate minus one and fails the Pocklington size bound. -/
theorem trial_part90_43719 :
    ((10^90 : ℕ) - 43719 - 1) % 55515720 = 0 ∧
      ¬ (10^90 : ℕ) - 43719 < (55515720 + 1)^2 := by
  decide +kernel

/-- The trial division part divides the candidate minus one and fails the Pocklington size bound. -/
theorem trial_part90_279 :
    ((10^90 : ℕ) - 279 - 1) % 11160 = 0 ∧
      ¬ (10^90 : ℕ) - 279 < (11160 + 1)^2 := by
  decide +kernel

#print axioms trial_part90_43719
#print axioms trial_part90_279

end LeanLab.DtRS1998.Diagnostics294
