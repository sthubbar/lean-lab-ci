/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212 and Table 2 page 214 row 300.
This checks only the closed right endpoint of the fixed coverage target.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a

namespace LeanLab.DtRS1998.Decomp455j

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- P0037 page 212, inclusion of the closed right endpoint.
The listed offset 6393 gives a prime complement at j = 500000000. -/
theorem endpoint : ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * 500000000 + a).Prime := by
  refine ⟨6393, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

#print axioms endpoint

end LeanLab.DtRS1998.Decomp455j
