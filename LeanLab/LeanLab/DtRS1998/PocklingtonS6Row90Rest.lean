/-
ROUTE BURST session 6, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib
import LeanLab.DtRS1998.PocklingtonB7Lucas
import LeanLab.DtRS1998.PocklingtonS6Row90P2G0
import LeanLab.DtRS1998.PocklingtonS6Row90Rest2

namespace LeanLab.DtRS1998.PocklingtonS6Row90Rest

/-- The hard candidates of row 10^90 still without a kernel certificate. -/
def rest : List ℕ := [999999999999999999999999999999999999999999999999999999999999999999999999999999999999962953, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999965227, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999974033]

open PocklingtonB7

/-- Every rest candidate of row 10^90 is in a p2 certificate group or in the rest list of PocklingtonS6Row90Rest2. -/
theorem rest_cover : ∀ q ∈ rest, q ∈ PocklingtonS6Row90P2G0.C.map lastP2 ∨ q ∈ PocklingtonS6Row90Rest2.rest := by
  decide +kernel

/-- P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^90. Proved in route burst session 6 p2 from
the kernel checked groups PocklingtonS6Row90P2G0, CONDITIONAL ON the LEAF PocklingtonS6Row90Rest2.rest_prime. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  intro q hq
  rcases rest_cover q hq with h | h
  · exact PocklingtonS6Row90P2G0.primes q h
  · exact PocklingtonS6Row90Rest2.rest_prime q h

#print axioms rest_prime

end LeanLab.DtRS1998.PocklingtonS6Row90Rest
