/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert8

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K9 : List ℕ := [1753, 270749, 749999999977]

/-- Pocklington entries for chunk 9, page 210. -/
def S9 : List Big.Cert := [(89999999997241, 7, [(2, 3), (3, 1), (5, 1), (749999999977, 1)]),
  (8363, 2, [(2, 1), (37, 1), (113, 1)]),
  (1505341, 2, [(2, 2), (3, 2), (5, 1), (8363, 1)]),
  (29893559, 11, [(2, 1), (37, 1), (613, 1)]),
  (89999999997239, 13, [(2, 1), (1505341, 1), (29893559, 1)]),
  (6961, 13, [(2, 4), (3, 1), (5, 1)]),
  (89999999997163, 2, [(2, 1), (3, 1), (983, 1), (6961, 1)]),
  (5411255411, 2, [(2, 1), (5, 1), (11, 1), (797, 1)]),
  (64935064933, 2, [(2, 2), (3, 1), (5411255411, 1)]),
  (89999999997139, 3, [(2, 1), (3, 2), (7, 1), (11, 1), (64935064933, 1)]),
  (89999999997137, 3, [(2, 4), (89, 1), (401, 1), (577, 1)]),
  (7499999999761, 14, [(2, 4), (3, 1), (5, 1), (47, 1), (1753, 1)]),
  (89999999997133, 2, [(2, 2), (3, 1), (7499999999761, 1)]),
  (1637, 2, [(2, 2), (409, 1)]),
  (9931109, 2, [(2, 2), (11, 1), (29, 1), (43, 1)]),
  (5624999999819, 2, [(2, 1), (173, 1), (1637, 1), (9931109, 1)]),
  (44999999998553, 3, [(2, 3), (5624999999819, 1)]),
  (89999999997107, 2, [(2, 1), (44999999998553, 1)]),
  (1182679, 3, [(2, 1), (3, 1), (7, 1), (29, 1)]),
  (4730717, 2, [(2, 2), (1182679, 1)]),
  (66230039, 7, [(2, 1), (7, 1), (4730717, 1)]),
  (89999999997101, 2, [(2, 2), (5, 2), (107, 1), (127, 1), (66230039, 1)]),
  (3617, 3, [(2, 5), (113, 1)]),
  (14999999999507, 2, [(2, 1), (23, 1), (31, 1), (491, 1), (3617, 1)]),
  (89999999997043, 13, [(2, 1), (3, 1), (14999999999507, 1)]),
  (10938259601, 3, [(2, 4), (5, 2), (101, 1), (270749, 1)]),
  (89999999997029, 2, [(2, 2), (11, 2), (17, 1), (10938259601, 1)]),
  (32059, 2, [(2, 1), (3, 2), (13, 1)]),
  (128237, 2, [(2, 2), (32059, 1)]),
  (114130931, 2, [(2, 1), (5, 1), (89, 1), (128237, 1)])]

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

end LeanLab.DtRS1998.Task303.High
