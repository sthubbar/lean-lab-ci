/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert12

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K13 : List ℕ := [576967459]

/-- Pocklington entries for chunk 13, page 210. -/
def S13 : List Big.Cert := [(59999999996329, 23, [(2, 3), (3, 1), (7, 1), (619, 1), (576967459, 1)]),
  (14627, 2, [(2, 1), (71, 1)]),
  (63481181, 2, [(2, 2), (5, 1), (7, 1), (31, 1), (14627, 1)]),
  (59999999996323, 5, [(2, 1), (3, 3), (23, 1), (761, 1), (63481181, 1)]),
  (535714285681, 53, [(2, 4), (3, 3), (5, 1), (7, 1), (17, 1), (19, 1)]),
  (59999999996273, 3, [(2, 4), (7, 1), (535714285681, 1)]),
  (10061, 3, [(2, 2), (5, 1), (503, 1)]),
  (271073723, 5, [(2, 1), (19, 1), (23, 1), (47, 1)]),
  (59999999996267, 2, [(2, 1), (11, 1), (10061, 1), (271073723, 1)]),
  (1621, 2, [(2, 2), (3, 4)]),
  (284724529, 17, [(2, 4), (3, 1), (11, 1), (73, 1)]),
  (59999999996171, 2, [(2, 1), (5, 1), (13, 1), (1621, 1), (284724529, 1)]),
  (1505343971, 6, [(2, 1), (5, 1), (13, 1), (19, 1), (61, 1)]),
  (59999999996119, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (73, 1), (1505343971, 1)]),
  (5987, 2, [(2, 1), (41, 1)]),
  (443039, 7, [(2, 1), (37, 1), (5987, 1)]),
  (59999999996063, 5, [(2, 1), (7, 2), (443039, 1)]),
  (59999999996047, 5, [(2, 1), (3, 1), (11, 1), (19, 1), (23, 1), (409, 1)]),
  (2467, 2, [(2, 1), (3, 2), (137, 1)]),
  (59999999996033, 3, [(2, 7), (61, 1), (239, 1), (2467, 1)]),
  (56897, 5, [(2, 6), (7, 1)]),
  (59999999995963, 2, [(2, 1), (3, 2), (13, 1), (56897, 1)]),
  (6709, 2, [(2, 2), (3, 1), (13, 1)]),
  (59999999995909, 11, [(2, 2), (3, 2), (7, 1), (23, 1), (6709, 1)]),
  (3163, 3, [(2, 1), (3, 1), (17, 1)]),
  (37957, 2, [(2, 2), (3, 1), (3163, 1)]),
  (5953, 7, [(2, 6), (3, 1)]),
  (5488667, 2, [(2, 1), (461, 1), (5953, 1)]),
  (9999999999313, 10, [(2, 4), (3, 1), (37957, 1), (5488667, 1)]),
  (59999999995879, 6, [(2, 1), (3, 1), (9999999999313, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle2
