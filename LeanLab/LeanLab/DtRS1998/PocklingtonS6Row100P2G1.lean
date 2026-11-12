/-
ROUTE BURST session 6 p2, DtRS1998 hard_prime. AI wrote this Lean code.
Binary Goldbach is OPEN.
P0037 Section 5.1 page 211, the finite primality certification paragraph,
and Table 1 page 213, row 10^100: kernel checked certificates for part of the
candidates listed in `PocklingtonS6Row100Rest.rest`, through the sound checker
`PocklingtonB7.chainB2`: Pocklington 1914, Brillhart Lehmer Selfridge 1975
Theorems 4 and 5, and the combined N - 1 and N + 1 Lucas test of PocklingtonB7Lucas.
The factorizations of N - 1 and N + 1 were found outside Lean with PARI/GP and
GMP-ECM up to B1 = 1e6; only the kernel check counts. No native_decide, no axioms.
-/

import LeanLab.DtRS1998.PocklingtonB7Lucas

namespace LeanLab.DtRS1998.PocklingtonS6Row100P2G1

open PocklingtonB7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Certificate chains, p2 group 1 of the rest candidates of row 10^100, P0037 Table 1 page 213. -/
def C : List (List Cert2) := [
  [(177427, 2, 0, [(2, 1), (3, 2), (9857, 1)], 0, 0, 0, 0, 0, []),
    (829865640205848419, 2, 0, [(2, 1), (73, 1), (101, 1), (177427, 1)], 0, 0, 0, 0, 0, []),
    (15426371, 2, 0, [(2, 1), (5, 1), (89, 1), (17333, 1)], 0, 0, 0, 0, 0, []),
    (308527421, 2, 0, [(2, 2), (5, 1), (15426371, 1)], 0, 0, 0, 0, 0, []),
    (215352139859, 2, 0, [(2, 1), (349, 1), (308527421, 1)], 0, 0, 0, 0, 0, []),
    (550585033004465500790771993699, 7, 0, [(2, 1), (7, 1), (13, 1), (379, 1), (215352139859, 1)], 0, 0, 0, 0, 0, []),
    (42945632574348309061680215508523, 2, 0, [(2, 1), (3, 1), (13, 1), (550585033004465500790771993699, 1)], 0, 0, 0, 0, 0, []),
    (9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999973873, 5, 0, [(2, 4), (3, 2), (7, 2), (829865640205848419, 1), (42945632574348309061680215508523, 1)], 0, 0, 0, 0, 0, [])],
  [(199819037986591, 6, 0, [(2, 1), (3, 1), (5, 1), (11, 1), (29, 1), (607, 1), (4973, 1)], 0, 0, 0, 0, 0, []),
    (3596742683758639, 3, 0, [(2, 1), (3, 2), (199819037986591, 1)], 0, 0, 0, 0, 0, []),
    (23070533, 2, 0, [(2, 2), (43, 1), (113, 1)], 0, 0, 0, 0, 0, []),
    (55678931893927, 3, 0, [(2, 1), (3, 3), (11, 1), (17, 1), (239, 1), (23070533, 1)], 0, 0, 0, 0, 0, []),
    (4844435720214209549, 2, 0, [(2, 2), (11, 1), (13, 1), (41, 1), (223, 1), (5431, 1)], 0, 0, 0, 0, 0, []),
    (3415359328686838004867480581959983027, 2, 0, [(2, 1), (13, 1), (487, 1), (55678931893927, 1), (4844435720214209549, 1)], 0, 0, 0, 0, 0, []),
    (9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999982229, 2, 0, [(2, 2), (3596742683758639, 1), (3415359328686838004867480581959983027, 1)], 0, 0, 0, 0, 0, [])]]

/-- P0037 Section 5.1 page 211, row 10^100: these candidates are prime,
checked by the kernel. -/
theorem primes : ∀ q ∈ C.map lastP2, q.Prime :=
  primes_of_chains2 C _ rfl (by decide +kernel)

#print axioms primes

end LeanLab.DtRS1998.PocklingtonS6Row100P2G1
