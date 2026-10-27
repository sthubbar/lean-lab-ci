/-
P0042 GvLtR 1989 Table 5, page 432: for consecutive primes q, q + d among the first 2000 odd
primes, how often E(q) < E(q + d), with the exceptional pairs. The lab's Python reproduced
every count of the table, all 20 rows, taking both primes among the first 2000 odd primes,
and every exceptional pair. Lean here, zero sorry: the exceptional pairs with q + d ≤ 397 go
the stated way, from the definition of E; and the pair printed (56,7) is not a prime pair,
FINDING F-0031, the pair meant is (5,7), whose E(5) = 1 < E(7) = 2.
Also page 432: the 271st odd prime is 1747. Run 20261018T1103Z-12430, unit U-0949.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.GvLtR1989.PaperTables

namespace LeanLab.GvLtR1989.Paper

open LeanLab.Verifications.Top50

set_option Elab.async false

/-- d = 2, exceptions with E(q) < E(q + 2), for q up to 239. -/
theorem t5_d2 : E 3 < E 5 ∧ E 5 < E 7 ∧ E 11 < E 13 ∧ E 17 < E 19 ∧ E 29 < E 31 ∧
    E 41 < E 43 ∧ E 71 < E 73 ∧ E 101 < E 103 ∧ E 191 < E 193 ∧ E 239 < E 241 := by
  decide +kernel

/-- d = 8 and d = 14 exceptions with q + d ≤ 397. -/
theorem t5_d8 : E 89 < E 97 ∧ E 359 < E 367 ∧ E 389 < E 397 ∧ E 113 < E 127 := by
  decide +kernel

/-- Non-exceptional twin pairs nearby go the usual way, E(q) > E(q + 2). -/
theorem t5_usual : E 59 > E 61 ∧ E 107 > E 109 ∧ E 137 > E 139 := by decide +kernel

/-- FINDING F-0031: the printed pair (56,7) is not a pair of primes. -/
theorem pair_56_7 : ¬ Nat.Prime 56 ∧ E 5 = 1 ∧ E 7 = 2 := by
  refine ⟨by norm_num, by decide +kernel, by decide +kernel⟩

/-- The 271st odd prime is 1747. -/
theorem odd_prime_271 : P10k[271]? = some 1747 := by decide +kernel

end LeanLab.GvLtR1989.Paper
