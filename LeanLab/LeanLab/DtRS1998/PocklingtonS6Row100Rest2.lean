/-
ROUTE BURST session 6, DtRS1998 hard_prime, p2. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/

import Mathlib

namespace LeanLab.DtRS1998.PocklingtonS6Row100Rest2

/-- The candidates of row 10^100 still without a kernel certificate after the p35 ECM pass. -/
def rest : List ℕ := [9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999960001, 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999960031]

/-- LEAF. P0037 Section 5.1 page 211, the finite primality certification
paragraph, and Table 1 page 213, row 10^100. These 2 candidates of the fixed
list are prime. PARI/GP reports each a BPSW probable prime, but GMP-ECM up to
B1 = 1e6 on N - 1 and N + 1 did not reach a factored part large enough for the
BLS cube root test or the combined N - 1 and N + 1 test, so their kernel
certificates remain OPEN. -/
theorem rest_prime : ∀ q ∈ rest, q.Prime := by
  sorry

end LeanLab.DtRS1998.PocklingtonS6Row100Rest2
