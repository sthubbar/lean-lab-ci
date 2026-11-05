/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert7

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K8 : List ℕ := [28597]

/-- Pocklington entries for chunk 8, page 210. -/
def S8 : List Big.Cert := [(64877, 3, [(2, 2), (7, 2), (331, 1)]),
  (3710575139, 2, [(2, 1), (28597, 1), (64877, 1)]),
  (59999999997631, 11, [(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (3710575139, 1)]),
  (1291, 2, [(2, 1), (3, 1), (5, 1), (43, 1)]),
  (3191, 11, [(2, 1), (5, 1), (11, 1)]),
  (59999999997629, 2, [(2, 2), (1291, 1), (3191, 1)]),
  (157217, 3, [(2, 5), (17, 3)]),
  (59999999997607, 3, [(2, 1), (3, 1), (229, 1), (157217, 1)]),
  (1049, 3, [(2, 3), (131, 1)]),
  (20981, 2, [(2, 2), (5, 1), (1049, 1)]),
  (59999999997593, 3, [(2, 3), (487, 1), (20981, 1)]),
  (47160913, 5, [(2, 4), (3, 1), (277, 1)]),
  (1414827391, 3, [(2, 1), (3, 1), (5, 1), (47160913, 1)]),
  (59999999997529, 13, [(2, 3), (3, 2), (19, 1), (31, 1), (1414827391, 1)]),
  (2437, 2, [(2, 2), (3, 1), (7, 1)]),
  (59999999997521, 3, [(2, 4), (5, 1), (11, 1), (17, 1), (383, 1), (2437, 1)]),
  (4597, 5, [(2, 2), (3, 1), (383, 1)]),
  (59999999997517, 5, [(2, 2), (3, 1), (47, 1), (101, 1), (4597, 1)]),
  (1217, 3, [(2, 6)]),
  (1487, 5, [(2, 1), (743, 1)]),
  (591827, 2, [(2, 1), (199, 1), (1487, 1)]),
  (15387503, 5, [(2, 1), (13, 1), (591827, 1)]),
  (30775007, 5, [(2, 1), (15387503, 1)]),
  (59999999997439, 3, [(2, 1), (3, 2), (89, 1), (1217, 1), (30775007, 1)]),
  (26387, 2, [(2, 1), (79, 1), (167, 1)]),
  (2957, 2, [(2, 2), (739, 1)]),
  (70969, 11, [(2, 3), (3, 1), (2957, 1)]),
  (12632483, 2, [(2, 1), (89, 1), (70969, 1)]),
  (75794899, 2, [(2, 1), (3, 1), (12632483, 1)]),
  (59999999997391, 3, [(2, 1), (3, 1), (5, 1), (26387, 1), (75794899, 1)])]

/-- Kernel acceptance of chunk 8, page 210. -/
theorem chain8 : Big.chainP K8 S8 = true := by decide +kernel

/-- Each entry of chunk 8 is prime, page 210. -/
theorem primes8 : ∀ c ∈ S8, c.1.Prime := by
  apply Big.chainP_sound S8 K8 ?_ chain8
  intro p hp
  have hm : K8.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7)))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7

#print axioms chain8
#print axioms primes8

end LeanLab.DtRS1998.Task303.Middle2
