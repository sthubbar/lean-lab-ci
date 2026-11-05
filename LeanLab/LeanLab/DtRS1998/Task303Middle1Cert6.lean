/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert5

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K6 : List ℕ := [8227067, 25353941]

/-- Pocklington entries for chunk 6, page 210. -/
def S6 : List Big.Cert := [(164541341, 2, [(2, 2), (5, 1), (8227067, 1)]),
  (19999999998551, 11, [(2, 1), (5, 2), (11, 1), (13, 1), (17, 1), (164541341, 1)]),
  (22067, 2, [(2, 1), (11, 1), (17, 1)]),
  (157349, 2, [(2, 2), (139, 1)]),
  (1888189, 6, [(2, 2), (3, 1), (157349, 1)]),
  (83333333327, 5, [(2, 1), (22067, 1), (1888189, 1)]),
  (1999999999849, 7, [(2, 3), (3, 1), (83333333327, 1)]),
  (19999999998491, 2, [(2, 1), (5, 1), (1999999999849, 1)]),
  (19999999998481, 11, [(2, 4), (3, 1), (5, 1), (83333333327, 1)]),
  (21341, 2, [(2, 2), (5, 1), (11, 1)]),
  (128047, 3, [(2, 1), (3, 1), (21341, 1)]),
  (6508027, 2, [(2, 1), (3, 5), (7, 1)]),
  (19999999998457, 5, [(2, 3), (3, 1), (128047, 1), (6508027, 1)]),
  (7721173, 5, [(2, 2), (3, 2), (139, 1)]),
  (9999999999221, 3, [(2, 2), (5, 1), (7, 1), (11, 1), (29, 2), (7721173, 1)]),
  (19999999998443, 2, [(2, 1), (9999999999221, 1)]),
  (2267, 2, [(2, 1), (11, 1), (103, 1)]),
  (10321, 7, [(2, 4), (3, 1), (5, 1)]),
  (1733929, 13, [(2, 3), (3, 1), (7, 1), (10321, 1)]),
  (6935717, 2, [(2, 2), (1733929, 1)]),
  (19999999998409, 13, [(2, 3), (3, 1), (53, 1), (2267, 1), (6935717, 1)]),
  (30497, 3, [(2, 5), (953, 1)]),
  (19999999998371, 2, [(2, 1), (5, 1), (7, 1), (31, 1), (30497, 1)]),
  (1825483753, 5, [(2, 3), (3, 2), (25353941, 1)]),
  (40160642567, 5, [(2, 1), (11, 1), (1825483753, 1)]),
  (19999999998367, 3, [(2, 1), (3, 1), (83, 1), (40160642567, 1)]),
  (1327, 3, [(2, 1), (3, 1), (13, 1)]),
  (5309, 2, [(2, 2), (1327, 1)]),
  (110799641, 6, [(2, 3), (5, 1), (7, 1), (19, 1), (59, 1)]),
  (19999999998347, 2, [(2, 1), (17, 1), (5309, 1), (110799641, 1)])]

/-- Kernel acceptance of chunk 6, page 210. -/
theorem chain6 : Big.chainP K6 S6 = true := by decide +kernel

/-- Each entry of chunk 6 is prime, page 210. -/
theorem primes6 : ∀ c ∈ S6, c.1.Prime := by
  apply Big.chainP_sound S6 K6 ?_ chain6
  intro p hp
  have hm : K6.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5)))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5

#print axioms chain6
#print axioms primes6

end LeanLab.DtRS1998.Task303.Middle1
