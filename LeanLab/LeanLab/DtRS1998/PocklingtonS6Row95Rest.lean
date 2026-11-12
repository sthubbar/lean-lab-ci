/-
ROUTE BURST session 6, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib

namespace LeanLab.DtRS1998.PocklingtonS6Row95Rest

/-- The hard candidates of row 10^95 still without a kernel certificate. -/
def rest : List ℕ := [99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999945701, 99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999971017]

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95. These 2 candidates of the fixed
list are prime. PARI/GP reports each a BPSW probable prime, but deep ECM on N - 1 and
N + 1 in route burst session 6 did not reach a factored part large enough for the
BLS cube root test or the combined N - 1 and N + 1 test, so their kernel
certificates remain OPEN. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  sorry

end LeanLab.DtRS1998.PocklingtonS6Row95Rest
