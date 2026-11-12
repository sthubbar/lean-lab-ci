/-
ROUTE BURST session 6 p3, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
P0037 Section 5.1 page 211, the finite primality certification paragraph,
and Table 1 page 213, row 10^90: kernel checked certificates for part of the
candidates listed in `PocklingtonS6Row90Rest2.rest`, through the sound checker
`PocklingtonB7.chainB2`: Pocklington 1914, Brillhart Lehmer Selfridge 1975
Theorems 4 and 5, and the combined N - 1 and N + 1 Lucas test of PocklingtonB7Lucas.
The factorizations of N - 1 and N + 1 were found outside Lean with PARI/GP and
GMP-ECM up to B1 = 3e6; only the kernel check counts. No native_decide, no axioms.
-/

import LeanLab.DtRS1998.PocklingtonB7Lucas

namespace LeanLab.DtRS1998.PocklingtonS6Row90P3G0

open PocklingtonB7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Certificate chains, p3 group 0 of the rest candidates of row 10^90, P0037 Table 1 page 213. -/
def C : List (List Cert2) := [
  [(2682777847, 3, 0, [(2, 1), (3, 1), (7, 1), (19, 1), (41, 1), (167, 1)], 0, 0, 0, 0, 0, []),
    (1337293, 5, 0, [(2, 2), (3, 2), (11, 2)], 0, 0, 0, 0, 0, []),
    (1414801, 14, 0, [(2, 4), (3, 3), (5, 2)], 0, 0, 0, 0, 0, []),
    (14148011, 2, 0, [(2, 1), (5, 1), (1414801, 1)], 0, 0, 0, 0, 0, []),
    (154738613, 2, 0, [(2, 2), (7, 1), (433, 1), (12763, 1)], 0, 0, 0, 0, 0, []),
    (87187, 3, 0, [(2, 1), (3, 1), (11, 1), (1321, 1)], 0, 0, 0, 0, 0, []),
    (77422057, 7, 0, [(2, 3), (3, 1), (37, 1), (87187, 1)], 0, 0, 0, 0, 0, []),
    (218617746259699, 3, 0, [(2, 1), (3, 3), (52291, 1), (77422057, 1)], 0, 0, 0, 0, 0, []),
    (27344707702163150921, 3, 0, [(2, 3), (5, 1), (53, 1), (59, 1), (218617746259699, 1)], 0, 0, 0, 0, 0, []),
    (38911747094577888800466673424092496951, 7, 0, [(2, 1), (5, 2), (13, 1), (14148011, 1), (154738613, 1), (27344707702163150921, 1)], 0, 0, 0, 0, 0, []),
    (999999999999999999999999999999999999999999999999999999999999999999999999999999999999965227, 2, 0, [(2, 1), (3, 1), (2682777847, 1)], 5, 48, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999965179, 604166666666666666666666666666666666666666666666666666666666666666666666666666666666645658, 35217499239641601167151864852593360084721920526302769331433443, [(2, 2), (11, 1), (163, 1), (14867, 1), (1337293, 1), (38911747094577888800466673424092496951, 1)])]]

/-- P0037 Section 5.1 page 211, row 10^90: these candidates are prime,
checked by the kernel. -/
theorem primes : ∀ q ∈ C.map lastP2, q.Prime :=
  primes_of_chains2 C _ rfl (by decide +kernel)

#print axioms primes

end LeanLab.DtRS1998.PocklingtonS6Row90P3G0
