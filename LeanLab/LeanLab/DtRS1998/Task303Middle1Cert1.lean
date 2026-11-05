/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert0

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K1 : List ℕ := [124847]

/-- Pocklington entries for chunk 1, page 210. -/
def S1 : List Big.Cert := [(2411, 6, [(2, 1), (5, 1), (241, 1)]),
  (19999999999829, 2, [(2, 2), (67, 1), (307, 1), (2411, 1)]),
  (2969, 3, [(2, 3), (7, 1)]),
  (5939, 2, [(2, 1), (2969, 1)]),
  (6029, 2, [(2, 2), (11, 1), (137, 1)]),
  (19999999999823, 5, [(2, 1), (19, 1), (5939, 1), (6029, 1)]),
  (3559, 3, [(2, 1), (3, 1), (593, 1)]),
  (35591, 17, [(2, 1), (5, 1), (3559, 1)]),
  (68192357, 2, [(2, 2), (479, 1), (35591, 1)]),
  (19999999999817, 3, [(2, 3), (61, 1), (601, 1), (68192357, 1)]),
  (1277, 2, [(2, 2), (11, 1)]),
  (8203445447, 7, [(2, 1), (7, 2), (1277, 1)]),
  (19999999999787, 2, [(2, 1), (23, 1), (53, 1), (8203445447, 1)]),
  (999999999989, 2, [(2, 2), (11, 1), (124847, 1)]),
  (19999999999781, 2, [(2, 2), (5, 1), (999999999989, 1)]),
  (79999999999, 6, [(2, 1), (3, 1), (163, 1), (409, 1)]),
  (19999999999751, 7, [(2, 1), (5, 3), (79999999999, 1)]),
  (1433, 3, [(2, 3), (179, 1)]),
  (3333333333283, 3, [(2, 1), (3, 1), (379, 2), (1433, 1)]),
  (19999999999699, 2, [(2, 1), (3, 1), (3333333333283, 1)]),
  (19999999999673, 3, [(2, 3), (7, 1), (11, 1), (17, 2), (31, 1)]),
  (12941, 2, [(2, 2), (5, 1), (647, 1)]),
  (16366612111, 11, [(2, 1), (3, 1), (5, 1), (12941, 1)]),
  (19999999999643, 2, [(2, 1), (13, 1), (47, 1), (16366612111, 1)]),
  (19813, 2, [(2, 2), (3, 1), (13, 1)]),
  (6023153, 3, [(2, 4), (19, 1), (19813, 1)]),
  (285714285709, 2, [(2, 2), (3, 1), (59, 1), (67, 1), (6023153, 1)]),
  (19999999999631, 7, [(2, 1), (5, 1), (7, 1), (285714285709, 1)]),
  (3329, 3, [(2, 8)]),
  (6659, 2, [(2, 1), (3329, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle1
