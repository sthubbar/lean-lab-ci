/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert12

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K13 : List ℕ := [6961849, 344827583]

/-- Pocklington entries for chunk 13, page 210. -/
def S13 : List Big.Cert := [(399999996281, 3, [(2, 3), (5, 1), (29, 1), (344827583, 1)]),
  (20751193, 5, [(2, 3), (3, 2), (7, 1), (11, 1)]),
  (399999996269, 2, [(2, 2), (61, 1), (79, 1), (20751193, 1)]),
  (3508771897, 5, [(2, 3), (3, 2), (7, 1), (6961849, 1)]),
  (399999996259, 2, [(2, 1), (3, 1), (19, 1), (3508771897, 1)]),
  (1481, 3, [(2, 3), (5, 1)]),
  (2791, 6, [(2, 1), (3, 2), (5, 1)]),
  (33493, 2, [(2, 2), (3, 1), (2791, 1)]),
  (1205749, 2, [(2, 2), (3, 2), (33493, 1)]),
  (399999996257, 3, [(2, 5), (7, 1), (1481, 1), (1205749, 1)]),
  (337669, 6, [(2, 2), (3, 1), (19, 1), (1481, 1)]),
  (2298850553, 3, [(2, 3), (23, 1), (37, 1), (337669, 1)]),
  (399999996223, 3, [(2, 1), (3, 1), (29, 1), (2298850553, 1)]),
  (130718953, 5, [(2, 3), (3, 2), (7, 1), (13, 1), (71, 1)]),
  (39999999619, 2, [(2, 1), (3, 2), (17, 1), (130718953, 1)]),
  (399999996191, 11, [(2, 1), (5, 1), (39999999619, 1)]),
  (399999996181, 13, [(2, 2), (3, 2), (5, 1), (17, 1), (130718953, 1)]),
  (13879, 6, [(2, 1), (3, 3), (257, 1)]),
  (721709, 2, [(2, 2), (13, 1), (13879, 1)]),
  (399999996161, 3, [(2, 8), (5, 1), (433, 1), (721709, 1)]),
  (3449, 3, [(2, 3), (431, 1)]),
  (399999996157, 5, [(2, 2), (3, 1), (43, 1), (3449, 1)]),
  (399999996133, 5, [(2, 2), (3, 1), (11, 2), (67, 1), (157, 1)]),
  (134138161, 7, [(2, 4), (3, 3), (5, 1), (13, 1)]),
  (399999996103, 3, [(2, 1), (3, 1), (7, 1), (71, 1), (134138161, 1)]),
  (1481481467, 2, [(2, 1), (241, 1), (311, 1)]),
  (399999996091, 3, [(2, 1), (3, 3), (5, 1), (1481481467, 1)]),
  (1979, 2, [(2, 1), (23, 1)]),
  (399999996079, 3, [(2, 1), (3, 1), (17, 1), (163, 1), (1979, 1)]),
  (399999996037, 5, [(2, 2), (3, 4), (127, 1), (487, 1)])]

/-- Kernel acceptance of chunk 13, page 210. -/
theorem chain13 : Big.chainP K13 S13 = true := by decide +kernel

/-- Each entry of chunk 13 is prime, page 210. -/
theorem primes13 : ∀ c ∈ S13, c.1.Prime := by
  apply Big.chainP_sound S13 K13 ?_ chain13
  intro p hp
  have hm : K13.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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

#print axioms chain13
#print axioms primes13

end LeanLab.DtRS1998.Task303.Low
