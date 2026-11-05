/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert10

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K11 : List ℕ := [282847]

/-- Pocklington entries for chunk 11, page 210. -/
def S11 : List Big.Cert := [(11313881, 3, [(2, 3), (5, 1), (282847, 1)]),
  (59999999996821, 2, [(2, 2), (3, 1), (5, 1), (13, 2), (523, 1), (11313881, 1)]),
  (1321, 13, [(2, 3), (3, 1), (5, 1)]),
  (2389, 2, [(2, 2), (3, 1), (199, 1)]),
  (97001, 3, [(2, 3), (5, 3)]),
  (3244295447, 5, [(2, 1), (7, 1), (2389, 1), (97001, 1)]),
  (59999999996819, 2, [(2, 1), (7, 1), (1321, 1), (3244295447, 1)]),
  (107142857137, 5, [(2, 4), (3, 3), (7, 1), (17, 1), (19, 1)]),
  (1071428571371, 2, [(2, 1), (5, 1), (107142857137, 1)]),
  (59999999996777, 3, [(2, 3), (7, 1), (1071428571371, 1)]),
  (1559, 19, [(2, 1), (19, 1), (41, 1)]),
  (3119, 7, [(2, 1), (1559, 1)]),
  (2557, 2, [(2, 2), (3, 2), (71, 1)]),
  (3206155819, 3, [(2, 1), (3, 1), (53, 1), (2557, 1)]),
  (59999999996767, 3, [(2, 1), (3, 1), (3119, 1), (3206155819, 1)]),
  (1031, 14, [(2, 1), (5, 1), (103, 1)]),
  (2399, 11, [(2, 1), (11, 1), (109, 1)]),
  (33587, 6, [(2, 1), (7, 1), (2399, 1)]),
  (746101619, 2, [(2, 1), (29, 1), (383, 1), (33587, 1)]),
  (59999999996743, 3, [(2, 1), (3, 1), (13, 1), (1031, 1), (746101619, 1)]),
  (105263157889, 13, [(2, 7), (3, 2), (7, 2), (17, 1)]),
  (59999999996731, 2, [(2, 1), (3, 1), (5, 1), (19, 1), (105263157889, 1)]),
  (813221, 2, [(2, 2), (5, 1), (73, 1)]),
  (59999999996723, 2, [(2, 1), (31, 1), (813221, 1)]),
  (56239, 3, [(2, 1), (3, 1), (7, 1), (13, 1)]),
  (59999999996701, 6, [(2, 2), (3, 4), (5, 2), (56239, 1)]),
  (9967, 3, [(2, 1), (3, 1), (11, 1), (151, 1)]),
  (3251, 6, [(2, 1), (5, 3)]),
  (3257503, 3, [(2, 1), (3, 1), (167, 1), (3251, 1)]),
  (501655463, 5, [(2, 1), (7, 1), (11, 1), (3257503, 1)])]

/-- Kernel acceptance of chunk 11, page 210. -/
theorem chain11 : Big.chainP K11 S11 = true := by decide +kernel

/-- Each entry of chunk 11 is prime, page 210. -/
theorem primes11 : ∀ c ∈ S11, c.1.Prime := by
  apply Big.chainP_sound S11 K11 ?_ chain11
  intro p hp
  have hm : K11.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
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
  · exact primes10 c h10

#print axioms chain11
#print axioms primes11

end LeanLab.DtRS1998.Task303.Middle2
