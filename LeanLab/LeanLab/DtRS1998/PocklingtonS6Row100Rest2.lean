/-
ROUTE BURST session 6, DtRS1998 hard_prime, p2. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib
import LeanLab.DtRS1998.PocklingtonB7Lucas
import LeanLab.DtRS1998.PocklingtonS6Row100P3G0

namespace LeanLab.DtRS1998.PocklingtonS6Row100Rest2

/-- The candidates of row 10^100 still without a kernel certificate after the p35 ECM pass. -/
def rest : List ℕ := [9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999960001, 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999960031]

open PocklingtonB7

/-- Every rest candidate of row 10^100 is in a p3 certificate group. -/
theorem rest_cover : ∀ q ∈ rest, q ∈ PocklingtonS6Row100P3G0.C.map lastP2 := by
  decide +kernel

/-- P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^100. Proved in route burst session 6 p3 from
the kernel checked groups PocklingtonS6Row100P3G0. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  intro q hq
  have h := rest_cover q hq
  · exact PocklingtonS6Row100P3G0.primes q h

#print axioms rest_prime

end LeanLab.DtRS1998.PocklingtonS6Row100Rest2
