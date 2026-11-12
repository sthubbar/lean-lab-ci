/-
ROUTE BURST session 6, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib
import LeanLab.DtRS1998.PocklingtonB7Lucas
import LeanLab.DtRS1998.PocklingtonS6Row95P2G0

namespace LeanLab.DtRS1998.PocklingtonS6Row95Rest

/-- The hard candidates of row 10^95 still without a kernel certificate. -/
def rest : List ℕ := [99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999945701, 99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999971017]

open PocklingtonB7

/-- Every rest candidate of row 10^95 is in a p2 certificate group. -/
theorem rest_cover : ∀ q ∈ rest, q ∈ PocklingtonS6Row95P2G0.C.map lastP2 := by
  decide +kernel

/-- P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^95. Proved in route burst session 6 p2 from
the kernel checked groups PocklingtonS6Row95P2G0. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  intro q hq
  have h := rest_cover q hq
  · exact PocklingtonS6Row95P2G0.primes q h

#print axioms rest_prime

end LeanLab.DtRS1998.PocklingtonS6Row95Rest
