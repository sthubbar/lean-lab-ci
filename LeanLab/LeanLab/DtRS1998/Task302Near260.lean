/-
AI wrote this Lean code for CODEX task302.
P0037 Section 5.2 page 212 and Table 2 page 214, row 10^260.
This constructed prime lies near the base and fits the small bitmap domain.
It is not asserted to be one of the printed table primes.
Full coverage remains OPEN. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Pock
import LeanLab.DtRS1998.Shift

namespace LeanLab.DtRS1998.Task302.Near260

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Explicit dependency-ordered Pocklington certificate data.
Supporting data for P0037 Section 5.2 page 212. -/
def S : List Big.Cert := [
  (1333019, 2, [(2, 1), (601, 1)]),
  (2666039, 17, [(2, 1), (1333019, 1)]),
  (42514669, 2, [(2, 2), (3, 2), (7, 1), (113, 1)]),
  (2767883, 2, [(2, 1), (13, 2), (19, 1)]),
  (2496630467, 2, [(2, 1), (11, 1), (41, 1), (2767883, 1)]),
  (29655840521167583, 5, [(2, 1), (1783, 1), (3331, 1), (2496630467, 1)]),
  (11587843, 3, [(2, 1), (3, 2), (7, 1), (91967, 1)]),
  (1060665311, 19, [(2, 1), (5, 1), (19, 1), (31, 2)]),
  (1506157, 2, [(2, 2), (3, 1), (313, 1)]),
  (2807476649, 3, [(2, 3), (233, 1), (1506157, 1)]),
  (8666401841, 3, [(2, 4), (5, 1), (23, 1), (83, 1)]),
  (784072293863563, 2, [(2, 1), (3, 2), (11, 2), (1361, 1), (1549, 1)]),
  (339410758966594017667547455058402038083572943677598628473416832635320690350034718979082980359, 14, [(2, 1), (13, 1), (29, 1), (11587843, 1), (1060665311, 1), (2807476649, 1), (8666401841, 1), (784072293863563, 1)]),
  (99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999998511601, 7, [(2, 3), (5, 1), (53, 1), (8269, 1), (2666039, 1), (42514669, 1), (29655840521167583, 1), (339410758966594017667547455058402038083572943677598628473416832635320690350034718979082980359, 1)])
]

#print axioms S

/-- Every Pocklington check in this nonempty chain accepts.
P0037 Section 5.2 page 212, supporting prime certification. -/
theorem accepted : Big.chainP [] S = true := by
  decide +kernel

#print axioms accepted

/-- Every prime field in the certified chain is prime.
P0037 Section 5.2 page 212, supporting prime certification. -/
theorem certified : ∀ c ∈ S, c.1.Prime :=
  Big.chainP_sound S [] (by simp) accepted

#print axioms certified

/-- A constructed prime below the base, with a fully checked Pocklington chain.
P0037 Section 5.2 page 212. This is not a claim about the printed q1. -/
theorem near_base_prime : (10 ^ 260 - 1488399).Prime := by
  rw [show 10 ^ 260 - 1488399 = 99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999998511601 by decide +kernel]
  exact certified (99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999998511601, 7, [(2, 3), (5, 1), (53, 1), (8269, 1), (2666039, 1), (42514669, 1), (29655840521167583, 1), (339410758966594017667547455058402038083572943677598628473416832635320690350034718979082980359, 1)]) (by decide +kernel)

#print axioms near_base_prime

/-- The candidate gap fits the lab bitmap bound over the entire interval width.
P0037 Section 5.2 page 212. This does not assert full coverage. -/
theorem usable_gap :
    0 < 1488399 ∧ 10 ^ 9 + 1488399 ≤ LeanLab.Verifications.Top50.Bits.B2 := by
  decide +kernel

#print axioms usable_gap

end LeanLab.DtRS1998.Task302.Near260
