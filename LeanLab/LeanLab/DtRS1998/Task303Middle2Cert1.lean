/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert0

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K1 : List ℕ := [15331, 163068293]

/-- Pocklington entries for chunk 1, page 210. -/
def S1 : List Big.Cert := [(59999999999593, 5, [(2, 3), (3, 1), (15331, 1), (163068293, 1)]),
  (7102609, 21, [(2, 4), (3, 1), (73, 1)]),
  (284104361, 3, [(2, 3), (5, 1), (7102609, 1)]),
  (59999999999591, 7, [(2, 1), (5, 1), (7, 2), (431, 1), (284104361, 1)]),
  (4951, 6, [(2, 1), (3, 2), (5, 2)]),
  (2019793981, 2, [(2, 2), (3, 1), (5, 1), (47, 1), (109, 1)]),
  (59999999999587, 2, [(2, 1), (3, 1), (4951, 1), (2019793981, 1)]),
  (14479, 3, [(2, 1), (3, 1), (19, 1), (127, 1)]),
  (39821, 2, [(2, 2), (5, 1), (11, 1)]),
  (86331929, 3, [(2, 3), (271, 1), (39821, 1)]),
  (14999999999893, 2, [(2, 2), (3, 1), (14479, 1), (86331929, 1)]),
  (59999999999573, 2, [(2, 2), (14999999999893, 1)]),
  (1741, 2, [(2, 2), (3, 1), (5, 1)]),
  (20611, 2, [(2, 1), (3, 2), (5, 1), (229, 1)]),
  (59999999999567, 5, [(2, 1), (11, 1), (1741, 1), (20611, 1)]),
  (59999999999521, 22, [(2, 5), (3, 1), (5, 1), (7, 1), (79, 1), (103, 1)]),
  (2617, 5, [(2, 3), (3, 1), (109, 1)]),
  (26171, 2, [(2, 1), (5, 1), (2617, 1)]),
  (18427, 2, [(2, 1), (3, 1), (37, 1)]),
  (7075969, 11, [(2, 7), (3, 1), (18427, 1)]),
  (382102327, 3, [(2, 1), (3, 3), (7075969, 1)]),
  (59999999999503, 6, [(2, 1), (3, 1), (26171, 1), (382102327, 1)]),
  (79273, 5, [(2, 3), (3, 3), (367, 1)]),
  (59999999999491, 3, [(2, 1), (3, 2), (5, 1), (47, 1), (79273, 1)]),
  (996649, 7, [(2, 3), (3, 1), (131, 1)]),
  (3585943103, 5, [(2, 1), (7, 1), (257, 1), (996649, 1)]),
  (29999999999699, 2, [(2, 1), (47, 1), (89, 1), (3585943103, 1)]),
  (59999999999399, 11, [(2, 1), (29999999999699, 1)]),
  (59999999999393, 3, [(2, 5), (617, 1), (631, 1)]),
  (81853, 11, [(2, 2), (3, 1), (19, 1), (359, 1)])]

/-- Kernel acceptance of chunk 1, page 210. -/
theorem chain1 : Big.chainP K1 S1 = true := by decide +kernel

/-- Each entry of chunk 1 is prime, page 210. -/
theorem primes1 : ∀ c ∈ S1, c.1.Prime := by
  apply Big.chainP_sound S1 K1 ?_ chain1
  intro p hp
  have hm : K1.all (fun p => S0.any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  exact primes0 c hc

#print axioms chain1
#print axioms primes1

end LeanLab.DtRS1998.Task303.Middle2
