/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert19

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K20 : List ℕ := [1031, 18043, 153953]

/-- Pocklington entries for chunk 20, page 210. -/
def S20 : List Big.Cert := [(923719, 6, [(2, 1), (3, 1), (153953, 1)]),
  (3694877, 2, [(2, 2), (923719, 1)]),
  (399999994267, 3, [(2, 1), (3, 1), (18043, 1), (3694877, 1)]),
  (17467, 3, [(2, 1), (3, 1), (41, 1)]),
  (399999994243, 2, [(2, 1), (3, 1), (17, 1), (17467, 1)]),
  (6203, 2, [(2, 1), (7, 1), (443, 1)]),
  (459023, 5, [(2, 1), (37, 1), (6203, 1)]),
  (52328623, 3, [(2, 1), (3, 1), (19, 1), (459023, 1)]),
  (399999994213, 2, [(2, 2), (3, 1), (7, 2), (13, 1), (52328623, 1)]),
  (96993209, 3, [(2, 3), (13, 1), (23, 2)]),
  (399999993917, 2, [(2, 2), (1031, 1), (96993209, 1)]),
  (15269, 2, [(2, 2), (11, 1), (347, 1)]),
  (30539, 2, [(2, 1), (15269, 1)]),
  (244313, 3, [(2, 3), (30539, 1)]),
  (749063659, 3, [(2, 1), (3, 1), (7, 1), (73, 1), (244313, 1)]),
  (399999993907, 3, [(2, 1), (3, 1), (89, 1), (749063659, 1)]),
  (4951, 6, [(2, 1), (3, 2), (5, 2)]),
  (399999993859, 3, [(2, 1), (3, 2), (103, 1), (4951, 1)]),
  (23293, 5, [(2, 2), (3, 2), (647, 1)]),
  (20544427, 2, [(2, 1), (3, 2), (7, 2), (23293, 1)]),
  (399999993691, 2, [(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (20544427, 1)]),
  (163673, 3, [(2, 3), (41, 1), (499, 1)]),
  (1964077, 2, [(2, 2), (3, 1), (163673, 1)]),
  (399999993667, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (373, 1), (1964077, 1)]),
  (5099569, 11, [(2, 4), (3, 1), (131, 1)]),
  (399999993223, 3, [(2, 1), (3, 1), (17, 1), (769, 1), (5099569, 1)])]

/-- Kernel acceptance of chunk 20, page 210. -/
theorem chain20 : Big.chainP K20 S20 = true := by decide +kernel

/-- Each entry of chunk 20 is prime, page 210. -/
theorem primes20 : ∀ c ∈ S20, c.1.Prime := by
  apply Big.chainP_sound S20 K20 ?_ chain20
  intro p hp
  have hm : K20.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15 ++ (S16 ++ (S17 ++ (S18 ++ (S19)))))))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
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
  · exact primes18 c h18
  · exact primes19 c h19

#print axioms chain20
#print axioms primes20

end LeanLab.DtRS1998.Task303.Low
