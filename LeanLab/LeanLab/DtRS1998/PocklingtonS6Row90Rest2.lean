/-
ROUTE BURST session 6, DtRS1998 hard_prime, p2. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib

namespace LeanLab.DtRS1998.PocklingtonS6Row90Rest2

/-- The candidates of row 10^90 still without a kernel certificate after the p35 ECM pass. -/
def rest : List ℕ := [999999999999999999999999999999999999999999999999999999999999999999999999999999999999965227]

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^90. This 1 candidate of the fixed
list is prime. PARI/GP reports it a BPSW probable prime, but GMP-ECM with B1 up to
3e6 on N - 1 and N + 1 did not reach a factored part large enough for the
BLS cube root test or the combined N - 1 and N + 1 test, so its kernel
certificate remains OPEN. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  sorry

end LeanLab.DtRS1998.PocklingtonS6Row90Rest2
