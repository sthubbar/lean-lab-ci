/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert16

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K17 : List ℕ := [1151, 24801587, 364963499]

/-- Pocklington entries for chunk 17, page 210. -/
def S17 : List Big.Cert := [(3571428529, 37, [(2, 4), (3, 2), (24801587, 1)]),
  (399999995249, 3, [(2, 4), (7, 1), (3571428529, 1)]),
  (399999995201, 3, [(2, 6), (5, 2), (13, 1), (331, 1)]),
  (7349, 2, [(2, 2), (11, 1), (167, 1)]),
  (132283, 2, [(2, 1), (3, 2), (7349, 1)]),
  (28308563, 2, [(2, 1), (107, 1), (132283, 1)]),
  (399999995191, 17, [(2, 1), (3, 2), (5, 1), (157, 1), (28308563, 1)]),
  (399999995183, 5, [(2, 1), (971, 1), (997, 1)]),
  (4793, 3, [(2, 3), (599, 1)]),
  (4745071, 3, [(2, 1), (3, 2), (5, 1), (11, 1), (4793, 1)]),
  (399999995159, 7, [(2, 1), (113, 1), (373, 1), (4745071, 1)]),
  (233551, 3, [(2, 1), (3, 3), (5, 2)]),
  (16666666463, 5, [(2, 1), (31, 1), (1151, 1), (233551, 1)]),
  (399999995113, 5, [(2, 3), (3, 1), (16666666463, 1)]),
  (29537, 3, [(2, 5), (13, 1)]),
  (24102193, 5, [(2, 4), (3, 1), (17, 1), (29537, 1)]),
  (399999995029, 2, [(2, 2), (3, 2), (461, 1), (24102193, 1)]),
  (3767, 5, [(2, 1), (7, 1), (269, 1)]),
  (856333, 2, [(2, 2), (3, 5)]),
  (6451612823, 5, [(2, 1), (3767, 1), (856333, 1)]),
  (399999995027, 2, [(2, 1), (31, 1), (6451612823, 1)]),
  (1663091, 2, [(2, 1), (5, 1), (11, 1), (13, 1)]),
  (399999994957, 5, [(2, 2), (3, 3), (17, 1), (131, 1), (1663091, 1)]),
  (199999997453, 2, [(2, 2), (137, 1), (364963499, 1)]),
  (399999994907, 2, [(2, 1), (199999997453, 1)]),
  (1567, 3, [(2, 1), (3, 3)]),
  (3867649, 23, [(2, 10), (3, 1)]),
  (399999994879, 3, [(2, 1), (3, 1), (11, 1), (1567, 1), (3867649, 1)]),
  (2825497, 5, [(2, 3), (3, 3), (103, 1)]),
  (11301989, 2, [(2, 2), (2825497, 1)])]

/-- Kernel acceptance of chunk 17, page 210. -/
theorem chain17 : Big.chainP K17 S17 = true := by decide +kernel

/-- Each entry of chunk 17 is prime, page 210. -/
theorem primes17 : ∀ c ∈ S17, c.1.Prime := by
  apply Big.chainP_sound S17 K17 ?_ chain17
  intro p hp
  have hm : K17.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15 ++ (S16))))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
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
  · exact primes14 c h14
  · exact primes15 c h15
  · exact primes16 c h16

#print axioms chain17
#print axioms primes17

end LeanLab.DtRS1998.Task303.Low
