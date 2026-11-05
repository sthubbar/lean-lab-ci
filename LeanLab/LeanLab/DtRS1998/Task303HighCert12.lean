/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert11

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K12 : List ℕ := [1831]

/-- Pocklington entries for chunk 12, page 210. -/
def S12 : List Big.Cert := [(10987, 2, [(2, 1), (3, 1), (1831, 1)]),
  (5688541, 2, [(2, 2), (3, 2), (5, 1), (11, 1), (13, 2)]),
  (2047874761, 29, [(2, 3), (3, 2), (5, 1), (5688541, 1)]),
  (89999999996429, 2, [(2, 2), (10987, 1), (2047874761, 1)]),
  (11579, 2, [(2, 1), (7, 1), (827, 1)]),
  (39199, 17, [(2, 1), (3, 1), (47, 1)]),
  (12700477, 5, [(2, 2), (3, 4), (39199, 1)]),
  (431816219, 2, [(2, 1), (17, 1), (12700477, 1)]),
  (89999999996419, 2, [(2, 1), (3, 2), (11579, 1), (431816219, 1)]),
  (1097, 3, [(2, 3), (137, 1)]),
  (89999999996381, 2, [(2, 2), (5, 1), (359, 1), (787, 1), (1097, 1)]),
  (932969, 3, [(2, 3), (139, 1)]),
  (1865939, 2, [(2, 1), (932969, 1)]),
  (13345195729, 7, [(2, 4), (3, 1), (149, 1), (1865939, 1)]),
  (89999999996377, 5, [(2, 3), (3, 1), (281, 1), (13345195729, 1)]),
  (89999999996341, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (157, 1), (263, 1)]),
  (546391, 15, [(2, 1), (3, 2), (5, 1), (13, 1)]),
  (89999999996329, 7, [(2, 3), (3, 2), (546391, 1)]),
  (89999999996251, 2, [(2, 1), (3, 1), (5, 4), (59, 1), (71, 1)]),
  (2203559, 7, [(2, 1), (7, 1), (107, 1)]),
  (4407119, 13, [(2, 1), (2203559, 1)]),
  (52885429, 10, [(2, 2), (3, 1), (4407119, 1)]),
  (12057877813, 5, [(2, 2), (3, 1), (19, 1), (52885429, 1)]),
  (89999999996233, 5, [(2, 3), (3, 1), (311, 1), (12057877813, 1)]),
  (1031, 14, [(2, 1), (5, 1), (103, 1)]),
  (2063, 5, [(2, 1), (1031, 1)]),
  (464539, 3, [(2, 1), (3, 1), (139, 1)]),
  (39021277, 5, [(2, 2), (3, 1), (7, 1), (464539, 1)]),
  (89999999996219, 2, [(2, 1), (13, 1), (43, 1), (2063, 1), (39021277, 1)]),
  (1733, 2, [(2, 2), (433, 1)])]

/-- Kernel acceptance of chunk 12, page 210. -/
theorem chain12 : Big.chainP K12 S12 = true := by decide +kernel

/-- Each entry of chunk 12 is prime, page 210. -/
theorem primes12 : ∀ c ∈ S12, c.1.Prime := by
  apply Big.chainP_sound S12 K12 ?_ chain12
  intro p hp
  have hm : K12.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11)))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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

#print axioms chain12
#print axioms primes12

end LeanLab.DtRS1998.Task303.High
