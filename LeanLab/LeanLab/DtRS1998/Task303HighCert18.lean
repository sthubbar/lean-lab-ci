/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert17

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K18 : List ℕ := [1039, 2741, 12391, 50767]

/-- Pocklington entries for chunk 18, page 210. -/
def S18 : List Big.Cert := [(106813769, 3, [(2, 3), (263, 1), (50767, 1)]),
  (89999999994173, 2, [(2, 2), (17, 1), (12391, 1), (106813769, 1)]),
  (11382521, 3, [(2, 3), (5, 1), (17, 1), (19, 1)]),
  (89999999994061, 10, [(2, 2), (3, 2), (5, 1), (13, 1), (31, 1), (109, 1), (11382521, 1)]),
  (53749249, 23, [(2, 9), (3, 1), (7, 1)]),
  (89999999994059, 6, [(2, 1), (7, 1), (11, 1), (83, 1), (131, 1), (53749249, 1)]),
  (21929, 3, [(2, 3), (2741, 1)]),
  (9868051, 2, [(2, 1), (3, 2), (5, 2), (21929, 1)]),
  (89999999993443, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (19, 1), (1039, 1), (9868051, 1)])]

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

end LeanLab.DtRS1998.Task303.High
