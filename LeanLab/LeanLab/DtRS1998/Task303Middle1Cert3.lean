/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert2

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K3 : List ℕ := [1033, 2459, 21871]

/-- Pocklington entries for chunk 3, page 210. -/
def S3 : List Big.Cert := [(107561579, 2, [(2, 1), (2459, 1), (21871, 1)]),
  (19999999999261, 10, [(2, 2), (3, 2), (5, 1), (1033, 1), (107561579, 1)]),
  (2083, 2, [(2, 1), (3, 1), (347, 1)]),
  (70823, 5, [(2, 1), (17, 1), (2083, 1)]),
  (12464849, 3, [(2, 4), (11, 1), (70823, 1)]),
  (99718793, 3, [(2, 3), (12464849, 1)]),
  (19999999999253, 2, [(2, 2), (7, 1), (13, 1), (19, 1), (29, 1), (99718793, 1)]),
  (7477, 2, [(2, 2), (3, 1), (7, 1), (89, 1)]),
  (416666666651, 6, [(2, 1), (5, 2), (13, 1), (7477, 1)]),
  (19999999999249, 11, [(2, 4), (3, 1), (416666666651, 1)]),
  (2861, 2, [(2, 2), (5, 1), (11, 1)]),
  (6343, 3, [(2, 1), (3, 1), (7, 1), (151, 1)]),
  (101489, 3, [(2, 4), (6343, 1)]),
  (16644197, 2, [(2, 2), (41, 1), (101489, 1)]),
  (19999999999141, 6, [(2, 2), (3, 1), (5, 1), (7, 1), (2861, 1), (16644197, 1)]),
  (10357, 2, [(2, 2), (3, 1), (863, 1)]),
  (1733, 2, [(2, 2), (433, 1)]),
  (137932937, 3, [(2, 3), (1733, 1)]),
  (19999999999127, 5, [(2, 1), (7, 1), (10357, 1), (137932937, 1)]),
  (1973, 2, [(2, 2), (17, 1)]),
  (19999999999121, 3, [(2, 4), (5, 1), (139, 1), (151, 1), (1973, 1)]),
  (1153, 5, [(2, 7)]),
  (19999999999117, 2, [(2, 2), (3, 4), (109, 1), (1153, 1)]),
  (950111, 7, [(2, 1), (5, 1), (7, 3)]),
  (666977923, 2, [(2, 1), (3, 3), (13, 1), (950111, 1)]),
  (19999999999079, 7, [(2, 1), (11, 1), (29, 1), (47, 1), (666977923, 1)]),
  (46441, 7, [(2, 3), (3, 3)]),
  (19999999999069, 2, [(2, 2), (3, 1), (367, 1), (46441, 1)]),
  (1019, 2, [(2, 1), (509, 1)]),
  (23148148147, 2, [(2, 1), (3, 1), (59, 1), (1019, 1)])]

/-- Kernel acceptance of chunk 3, page 210. -/
theorem chain3 : Big.chainP K3 S3 = true := by decide +kernel

/-- Each entry of chunk 3 is prime, page 210. -/
theorem primes3 : ∀ c ∈ S3, c.1.Prime := by
  apply Big.chainP_sound S3 K3 ?_ chain3
  intro p hp
  have hm : K3.all (fun p => (S0 ++ (S1 ++ (S2))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2

#print axioms chain3
#print axioms primes3

end LeanLab.DtRS1998.Task303.Middle1
