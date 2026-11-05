/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert3

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K4 : List ℕ := [23148148147]

/-- Pocklington entries for chunk 4, page 210. -/
def S4 : List Big.Cert := [(833333333293, 2, [(2, 2), (3, 2), (23148148147, 1)]),
  (19999999999033, 7, [(2, 3), (3, 1), (833333333293, 1)]),
  (1759, 6, [(2, 1), (3, 1), (293, 1)]),
  (31663, 3, [(2, 1), (3, 2), (1759, 1)]),
  (19999999999019, 2, [(2, 1), (13, 1), (37, 1), (31663, 1)]),
  (1867, 2, [(2, 1), (3, 1), (311, 1)]),
  (19999999998931, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (173, 1), (1867, 1)]),
  (102040816321, 7, [(2, 6), (3, 2), (5, 1), (17, 1), (19, 1)]),
  (19999999998917, 3, [(2, 2), (7, 2), (102040816321, 1)]),
  (61328623, 3, [(2, 1), (3, 1), (17, 1), (179, 1)]),
  (245314493, 2, [(2, 2), (61328623, 1)]),
  (1471886959, 17, [(2, 1), (3, 1), (245314493, 1)]),
  (19999999998893, 2, [(2, 2), (43, 1), (79, 1), (1471886959, 1)]),
  (7591, 6, [(2, 1), (3, 1), (5, 1), (11, 1)]),
  (25353941, 2, [(2, 2), (5, 1), (167, 1), (7591, 1)]),
  (1673360107, 11, [(2, 1), (3, 1), (11, 1), (25353941, 1)]),
  (1111111111049, 3, [(2, 3), (83, 1), (1673360107, 1)]),
  (19999999998883, 3, [(2, 1), (3, 2), (1111111111049, 1)]),
  (6997, 5, [(2, 2), (3, 1), (11, 1)]),
  (1175497, 5, [(2, 3), (3, 1), (7, 1), (6997, 1)]),
  (18018018017, 3, [(2, 5), (479, 1), (1175497, 1)]),
  (19999999998871, 3, [(2, 1), (3, 1), (5, 1), (37, 1), (18018018017, 1)]),
  (2521, 17, [(2, 3), (3, 2)]),
  (3398309, 2, [(2, 2), (337, 1), (2521, 1)]),
  (2732240437, 2, [(2, 2), (3, 1), (67, 1), (3398309, 1)]),
  (19999999998841, 23, [(2, 3), (3, 1), (5, 1), (61, 1), (2732240437, 1)]),
  (1543, 5, [(2, 1), (3, 1), (257, 1)]),
  (6173, 2, [(2, 2), (1543, 1)]),
  (1619957881, 19, [(2, 3), (3, 4), (5, 1), (17, 1)]),
  (19999999998827, 2, [(2, 1), (6173, 1), (1619957881, 1)])]

/-- Kernel acceptance of chunk 4, page 210. -/
theorem chain4 : Big.chainP K4 S4 = true := by decide +kernel

/-- Each entry of chunk 4 is prime, page 210. -/
theorem primes4 : ∀ c ∈ S4, c.1.Prime := by
  apply Big.chainP_sound S4 K4 ?_ chain4
  intro p hp
  have hm : K4.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3)))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3

#print axioms chain4
#print axioms primes4

end LeanLab.DtRS1998.Task303.Middle1
