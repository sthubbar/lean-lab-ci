/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert9

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K10 : List ℕ := [1367, 802643]

/-- Pocklington entries for chunk 10, page 210. -/
def S10 : List Big.Cert := [(11237003, 2, [(2, 1), (7, 1), (802643, 1)]),
  (19999999997503, 5, [(2, 1), (3, 1), (7, 1), (31, 1), (1367, 1), (11237003, 1)]),
  (8663, 5, [(2, 1), (61, 1)]),
  (577167263, 7, [(2, 1), (7, 1), (199, 1), (223, 1)]),
  (19999999997477, 2, [(2, 2), (8663, 1), (577167263, 1)]),
  (95456281, 17, [(2, 3), (3, 1), (5, 1), (103, 1)]),
  (8591065291, 2, [(2, 1), (3, 2), (5, 1), (95456281, 1)]),
  (19999999997449, 7, [(2, 3), (3, 1), (97, 1), (8591065291, 1)]),
  (1487, 5, [(2, 1), (743, 1)]),
  (1889, 3, [(2, 5), (59, 1)]),
  (370370370323, 2, [(2, 1), (1487, 1), (1889, 1)]),
  (19999999997443, 3, [(2, 1), (3, 3), (370370370323, 1)]),
  (7547, 2, [(2, 1), (7, 3)]),
  (110419151, 13, [(2, 1), (5, 2), (41, 1), (61, 1)]),
  (1325029813, 2, [(2, 2), (3, 1), (110419151, 1)]),
  (19999999997423, 5, [(2, 1), (7547, 1), (1325029813, 1)]),
  (13865779, 2, [(2, 1), (3, 2), (17, 1), (113, 1)]),
  (55463117, 2, [(2, 2), (13865779, 1)]),
  (2773155851, 2, [(2, 1), (5, 2), (55463117, 1)]),
  (19999999997413, 2, [(2, 2), (3, 1), (601, 1), (2773155851, 1)]),
  (971250971, 6, [(2, 1), (5, 1), (17, 3)]),
  (7770007769, 3, [(2, 3), (971250971, 1)]),
  (19999999997407, 5, [(2, 1), (3, 2), (11, 1), (13, 1), (7770007769, 1)]),
  (21149, 3, [(2, 2), (17, 1), (311, 1)]),
  (30427, 5, [(2, 1), (3, 1), (11, 1), (461, 1)]),
  (31522373, 2, [(2, 2), (7, 1), (37, 1), (30427, 1)]),
  (19999999997311, 6, [(2, 1), (3, 1), (5, 1), (21149, 1), (31522373, 1)]),
  (297991537, 5, [(2, 4), (3, 1), (59, 1), (139, 1)]),
  (19999999997293, 5, [(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (297991537, 1)]),
  (1999999999729, 17, [(2, 4), (3, 3), (29, 1), (137, 1)])]

/-- Kernel acceptance of chunk 10, page 210. -/
theorem chain10 : Big.chainP K10 S10 = true := by decide +kernel

/-- Each entry of chunk 10 is prime, page 210. -/
theorem primes10 : ∀ c ∈ S10, c.1.Prime := by
  apply Big.chainP_sound S10 K10 ?_ chain10
  intro p hp
  have hm : K10.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9)))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7
  · exact primes8 c h8
  · exact primes9 c h9

#print axioms chain10
#print axioms primes10

end LeanLab.DtRS1998.Task303.Middle1
