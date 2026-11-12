/-
ROUTE BURST session 6 p2, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
P0037 Section 5.1 page 211, the finite primality certification paragraph,
and Table 1 page 213, row 10^95: kernel checked certificates for part of the
candidates listed in `PocklingtonS6Row95Rest.rest`, through the sound checker
`PocklingtonB7.chainB2`: Pocklington 1914, Brillhart Lehmer Selfridge 1975
Theorems 4 and 5, and the combined N - 1 and N + 1 Lucas test of PocklingtonB7Lucas.
The factorizations of N - 1 and N + 1 were found outside Lean with PARI/GP and
GMP-ECM up to B1 = 1e6; only the kernel check counts. No native_decide, no axioms.
-/

import LeanLab.DtRS1998.PocklingtonB7Lucas

namespace LeanLab.DtRS1998.PocklingtonS6Row95P2G0

open PocklingtonB7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Certificate chains, p2 group 0 of the rest candidates of row 10^95, P0037 Table 1 page 213. -/
def C : List (List Cert2) := [
  [(165219380471, 13, 0, [(2, 1), (5, 1), (631, 1), (2677, 1)], 0, 0, 0, 0, 0, []),
    (75989, 2, 0, [(2, 2), (11, 2)], 0, 0, 0, 0, 0, []),
    (394990823, 5, 0, [(2, 1), (23, 1), (113, 1), (75989, 1)], 0, 0, 0, 0, 0, []),
    (17466299821, 2, 0, [(2, 2), (3, 2), (5, 1), (23, 2), (59, 1)], 0, 0, 0, 0, 0, []),
    (114712793298421695313, 5, 0, [(2, 4), (3, 1), (13, 1), (661, 1), (15923, 1), (17466299821, 1)], 0, 0, 0, 0, 0, []),
    (186790273336870829086457109833747551, 3, 0, [(2, 1), (3, 2), (5, 2), (9161, 1), (394990823, 1), (114712793298421695313, 1)], 0, 0, 0, 0, 0, []),
    (99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999945701, 2, 0, [(2, 2), (5, 2), (1097, 1), (165219380471, 1), (186790273336870829086457109833747551, 1)], 0, 0, 0, 0, 0, [])],
  [(8421079, 3, 0, [(2, 1), (3, 1), (29, 1), (48397, 1)], 0, 0, 0, 0, 0, []),
    (5392136413501, 2, 0, [(2, 2), (3, 1), (5, 3), (4091, 1)], 0, 0, 0, 0, 0, []),
    (1891323257, 3, 0, [(2, 3), (191, 1), (937, 1)], 0, 0, 0, 0, 0, []),
    (2363416455179771, 6, 0, [(2, 1), (5, 1), (29, 1), (31, 1), (139, 1), (1891323257, 1)], 0, 0, 0, 0, 0, []),
    (318846275067407192868432352282979779, 2, 0, [(2, 1), (3, 2), (7, 1), (97, 1), (2363416455179771, 1)], 0, 0, 0, 0, 0, []),
    (99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999971017, 5, 0, [(2, 3), (3, 1), (11, 1), (1459, 1), (8421079, 1)], 8, 46, 99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999970971, 54347826086956521739130434782608695652173913043478260869565217391304347826086956521739130419031, 4930690459141857458968377217904302116265791765997470407543089, [(2, 1), (5392136413501, 1), (318846275067407192868432352282979779, 1)])]]

/-- P0037 Section 5.1 page 211, row 10^95: these candidates are prime,
checked by the kernel. -/
theorem primes : ∀ q ∈ C.map lastP2, q.Prime :=
  primes_of_chains2 C _ rfl (by decide +kernel)

#print axioms primes

end LeanLab.DtRS1998.PocklingtonS6Row95P2G0
