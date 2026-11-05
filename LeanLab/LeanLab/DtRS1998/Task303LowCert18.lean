/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert17

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K18 : List ℕ := [11301989]

/-- Pocklington entries for chunk 18, page 210. -/
def S18 : List Big.Cert := [(2531645537, 5, [(2, 5), (7, 1), (11301989, 1)]),
  (399999994847, 5, [(2, 1), (79, 1), (2531645537, 1)]),
  (7411, 2, [(2, 1), (3, 1), (5, 1), (13, 1)]),
  (399999994843, 2, [(2, 1), (3, 1), (7, 1), (53, 1), (7411, 1)]),
  (16001, 3, [(2, 7)]),
  (672043, 7, [(2, 1), (3, 1), (7, 1), (16001, 1)]),
  (322580641, 21, [(2, 5), (3, 1), (5, 1), (672043, 1)]),
  (399999994841, 6, [(2, 3), (5, 1), (31, 1), (322580641, 1)]),
  (1373, 2, [(2, 2), (7, 3)]),
  (91961, 3, [(2, 3), (5, 1), (11, 2)]),
  (735689, 3, [(2, 3), (91961, 1)]),
  (399999994813, 5, [(2, 2), (3, 2), (11, 1), (1373, 1), (735689, 1)]),
  (29069767, 5, [(2, 1), (3, 4), (11, 2)]),
  (465116273, 3, [(2, 4), (29069767, 1)]),
  (399999994781, 2, [(2, 2), (5, 1), (43, 1), (465116273, 1)]),
  (399999994777, 7, [(2, 3), (3, 2), (19, 1), (599, 1)]),
  (1039, 3, [(2, 1), (3, 1), (173, 1)]),
  (3318841, 31, [(2, 3), (3, 3), (5, 1), (7, 1)]),
  (192492779, 2, [(2, 1), (29, 1), (3318841, 1)]),
  (399999994763, 2, [(2, 1), (1039, 1), (192492779, 1)]),
  (13883, 2, [(2, 1), (11, 1), (631, 1)]),
  (13049, 3, [(2, 3), (7, 1), (233, 1)]),
  (1200509, 2, [(2, 2), (23, 1), (13049, 1)]),
  (399999994729, 7, [(2, 3), (3, 1), (13883, 1), (1200509, 1)]),
  (1559, 19, [(2, 1), (19, 1), (41, 1)]),
  (399999994717, 2, [(2, 2), (3, 1), (7, 1), (31, 1), (37, 1), (1559, 1)]),
  (399999994711, 6, [(2, 1), (3, 1), (5, 1), (191, 1), (349, 1)]),
  (827633, 3, [(2, 4), (13, 1), (23, 1)]),
  (399999994699, 2, [(2, 1), (3, 1), (109, 1), (739, 1), (827633, 1)]),
  (49999999337, 3, [(2, 3), (7, 1), (79, 1), (11301989, 1)])]

/-- Kernel acceptance of chunk 18, page 210. -/
theorem chain18 : Big.chainP K18 S18 = true := by decide +kernel

/-- Each entry of chunk 18 is prime, page 210. -/
theorem primes18 : ∀ c ∈ S18, c.1.Prime := by
  apply Big.chainP_sound S18 K18 ?_ chain18
  intro p hp
  have hm : K18.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15 ++ (S16 ++ (S17)))))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17
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
  · exact primes17 c h17

#print axioms chain18
#print axioms primes18

end LeanLab.DtRS1998.Task303.Low
