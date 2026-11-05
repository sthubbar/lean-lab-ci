/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert1

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K2 : List ℕ := [6659]

/-- Pocklington entries for chunk 2, page 210. -/
def S2 : List Big.Cert := [(19999999999549, 6, [(2, 2), (3, 3), (31, 1), (47, 1), (6659, 1)]),
  (7331, 2, [(2, 1), (5, 1), (733, 1)]),
  (66553, 10, [(2, 3), (3, 1), (47, 1)]),
  (16238933, 2, [(2, 2), (61, 1), (66553, 1)]),
  (97433599, 3, [(2, 1), (3, 1), (16238933, 1)]),
  (1428571428539, 2, [(2, 1), (7331, 1), (97433599, 1)]),
  (19999999999547, 2, [(2, 1), (7, 1), (1428571428539, 1)]),
  (111509, 2, [(2, 2), (61, 1), (457, 1)]),
  (19999999999481, 3, [(2, 3), (5, 1), (19, 1), (111509, 1)]),
  (19999999999471, 3, [(2, 1), (3, 1), (5, 1), (283, 1), (701, 1)]),
  (14033, 3, [(2, 4), (877, 1)]),
  (5882352941, 2, [(2, 2), (5, 1), (14033, 1)]),
  (9999999999701, 2, [(2, 2), (5, 2), (17, 1), (5882352941, 1)]),
  (19999999999403, 2, [(2, 1), (9999999999701, 1)]),
  (33461, 3, [(2, 2), (5, 1), (7, 1), (239, 1)]),
  (1070753, 3, [(2, 5), (33461, 1)]),
  (391895599, 3, [(2, 1), (3, 1), (61, 1), (1070753, 1)]),
  (19999999999367, 5, [(2, 1), (17, 1), (19, 1), (79, 1), (391895599, 1)]),
  (1523, 2, [(2, 1), (761, 1)]),
  (7867, 3, [(2, 1), (3, 2), (19, 1)]),
  (5947453, 2, [(2, 2), (3, 3), (7, 1), (7867, 1)]),
  (95159249, 3, [(2, 4), (5947453, 1)]),
  (19999999999327, 5, [(2, 1), (3, 1), (23, 1), (1523, 1), (95159249, 1)]),
  (42701, 3, [(2, 2), (5, 2), (7, 1)]),
  (234186553, 5, [(2, 3), (3, 4), (19, 1), (23, 1)]),
  (19999999999307, 2, [(2, 1), (42701, 1), (234186553, 1)]),
  (1033, 5, [(2, 3), (3, 1), (43, 1)]),
  (1229, 2, [(2, 2), (307, 1)]),
  (2459, 2, [(2, 1), (1229, 1)]),
  (21871, 6, [(2, 1), (3, 7)])]

/-- Kernel acceptance of chunk 2, page 210. -/
theorem chain2 : Big.chainP K2 S2 = true := by decide +kernel

/-- Each entry of chunk 2 is prime, page 210. -/
theorem primes2 : ∀ c ∈ S2, c.1.Prime := by
  apply Big.chainP_sound S2 K2 ?_ chain2
  intro p hp
  have hm : K2.all (fun p => (S0 ++ (S1)).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1
  · exact primes0 c h0
  · exact primes1 c h1

#print axioms chain2
#print axioms primes2

end LeanLab.DtRS1998.Task303.Middle1
