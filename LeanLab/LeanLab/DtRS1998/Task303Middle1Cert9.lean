/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert8

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K9 : List ℕ := [1039]

/-- Pocklington entries for chunk 9, page 210. -/
def S9 : List Big.Cert := [(2953, 13, [(2, 3), (3, 2)]),
  (19999999997851, 3, [(2, 1), (3, 1), (5, 2), (1039, 1), (2953, 1)]),
  (13267, 3, [(2, 1), (3, 2), (11, 1)]),
  (53069, 2, [(2, 2), (13267, 1)]),
  (742967, 5, [(2, 1), (7, 1), (53069, 1)]),
  (19999999997833, 5, [(2, 3), (3, 1), (742967, 1)]),
  (1871, 14, [(2, 1), (5, 1), (11, 1)]),
  (19999999997771, 2, [(2, 1), (5, 1), (13, 1), (19, 1), (1871, 1)]),
  (33857, 3, [(2, 6), (23, 2)]),
  (2499999999719, 23, [(2, 1), (13, 1), (29, 1), (33857, 1)]),
  (19999999997753, 3, [(2, 3), (2499999999719, 1)]),
  (1787, 2, [(2, 1), (19, 1), (47, 1)]),
  (64333, 2, [(2, 2), (3, 2), (1787, 1)]),
  (82474907, 2, [(2, 1), (641, 1), (64333, 1)]),
  (19999999997687, 5, [(2, 1), (29, 1), (37, 1), (113, 1), (82474907, 1)]),
  (11813, 2, [(2, 2), (2953, 1)]),
  (23627, 2, [(2, 1), (11813, 1)]),
  (1063, 3, [(2, 1), (3, 2), (59, 1)]),
  (839771, 2, [(2, 1), (5, 1), (79, 1), (1063, 1)]),
  (47027177, 3, [(2, 3), (7, 1), (839771, 1)]),
  (19999999997623, 19, [(2, 1), (3, 2), (23627, 1), (47027177, 1)]),
  (2499999999701, 10, [(2, 2), (5, 2), (7, 1), (359, 1), (367, 1)]),
  (19999999997609, 3, [(2, 3), (2499999999701, 1)]),
  (2803, 2, [(2, 1), (3, 1), (467, 1)]),
  (61667, 2, [(2, 1), (11, 1), (2803, 1)]),
  (28983491, 2, [(2, 1), (5, 1), (47, 1), (61667, 1)]),
  (19999999997569, 13, [(2, 7), (3, 2), (599, 1), (28983491, 1)]),
  (1367, 5, [(2, 1), (683, 1)]),
  (401321, 3, [(2, 3), (5, 1), (79, 1)]),
  (802643, 2, [(2, 1), (401321, 1)])]

/-- Kernel acceptance of chunk 9, page 210. -/
theorem chain9 : Big.chainP K9 S9 = true := by decide +kernel

/-- Each entry of chunk 9 is prime, page 210. -/
theorem primes9 : ∀ c ∈ S9, c.1.Prime := by
  apply Big.chainP_sound S9 K9 ?_ chain9
  intro p hp
  have hm : K9.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7
  · exact primes8 c h8

#print axioms chain9
#print axioms primes9

end LeanLab.DtRS1998.Task303.Middle1
