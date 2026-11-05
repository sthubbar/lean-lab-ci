/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert13

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K14 : List ℕ := [14033]

/-- Pocklington entries for chunk 14, page 210. -/
def S14 : List Big.Cert := [(389099, 2, [(2, 1), (257, 1), (757, 1)]),
  (171203561, 3, [(2, 3), (5, 1), (11, 1), (389099, 1)]),
  (101010100991, 7, [(2, 1), (5, 1), (59, 1), (171203561, 1)]),
  (19999999996219, 2, [(2, 1), (3, 2), (11, 1), (101010100991, 1)]),
  (1427, 2, [(2, 1), (23, 1)]),
  (19999999996213, 2, [(2, 2), (3, 1), (19, 1), (503, 1), (1427, 1)]),
  (65855329, 38, [(2, 5), (3, 1), (7, 1), (11, 1), (59, 1)]),
  (185185185149, 2, [(2, 2), (19, 1), (37, 1), (65855329, 1)]),
  (370370370299, 2, [(2, 1), (185185185149, 1)]),
  (19999999996147, 5, [(2, 1), (3, 3), (370370370299, 1)]),
  (27548209361, 3, [(2, 4), (5, 1), (7, 1), (797, 1)]),
  (19999999996087, 3, [(2, 1), (3, 1), (11, 2), (27548209361, 1)]),
  (1013, 3, [(2, 2), (11, 1)]),
  (19999999996061, 2, [(2, 2), (5, 1), (7, 1), (19, 1), (23, 1), (1013, 1)]),
  (2197609, 13, [(2, 3), (3, 1), (7, 1), (103, 1)]),
  (2637130801, 13, [(2, 4), (3, 1), (5, 2), (2197609, 1)]),
  (15822784807, 3, [(2, 1), (3, 1), (2637130801, 1)]),
  (19999999996049, 3, [(2, 4), (79, 1), (15822784807, 1)]),
  (1723, 3, [(2, 1), (3, 1), (7, 1)]),
  (6356879, 7, [(2, 1), (11, 1), (17, 1), (23, 1)]),
  (19999999996043, 2, [(2, 1), (11, 1), (83, 1), (1723, 1), (6356879, 1)]),
  (4549, 6, [(2, 2), (3, 1), (379, 1)]),
  (9829, 2, [(2, 2), (3, 3)]),
  (19999999996027, 3, [(2, 1), (3, 1), (4549, 1), (9829, 1)]),
  (19999999996001, 3, [(2, 5), (5, 3), (17, 1), (14033, 1)]),
  (13693, 6, [(2, 2), (3, 1), (7, 1), (163, 1)]),
  (54773, 2, [(2, 2), (13693, 1)]),
  (19999999995931, 3, [(2, 1), (3, 3), (5, 1), (54773, 1)]),
  (19999999995809, 3, [(2, 5), (7, 1), (67, 1), (179, 1), (919, 1)]),
  (7933, 2, [(2, 2), (3, 1), (661, 1)])]

/-- Kernel acceptance of chunk 14, page 210. -/
theorem chain14 : Big.chainP K14 S14 = true := by decide +kernel

/-- Each entry of chunk 14 is prime, page 210. -/
theorem primes14 : ∀ c ∈ S14, c.1.Prime := by
  apply Big.chainP_sound S14 K14 ?_ chain14
  intro p hp
  have hm : K14.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13)))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
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
  · exact primes11 c h11
  · exact primes12 c h12
  · exact primes13 c h13

#print axioms chain14
#print axioms primes14

end LeanLab.DtRS1998.Task303.Middle1
