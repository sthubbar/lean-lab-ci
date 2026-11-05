/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert14

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K15 : List ℕ := [1297]

/-- Pocklington entries for chunk 15, page 210. -/
def S15 : List Big.Cert := [(1409, 3, [(2, 7)]),
  (147859, 2, [(2, 1), (3, 1), (19, 1), (1297, 1)]),
  (1666666649, 3, [(2, 3), (1409, 1), (147859, 1)]),
  (399999995761, 17, [(2, 4), (3, 1), (5, 1), (1666666649, 1)]),
  (17417, 3, [(2, 3), (7, 1), (311, 1)]),
  (1184357, 2, [(2, 2), (17, 1), (17417, 1)]),
  (399999995753, 5, [(2, 3), (7, 1), (37, 1), (163, 1), (1184357, 1)]),
  (399999995713, 5, [(2, 6), (3, 4), (97, 1), (103, 1)]),
  (1303, 6, [(2, 1), (3, 1), (7, 1)]),
  (5714285653, 5, [(2, 2), (3, 2), (43, 1), (1303, 1)]),
  (399999995711, 14, [(2, 1), (5, 1), (7, 1), (5714285653, 1)]),
  (5953, 7, [(2, 6), (3, 1)]),
  (23813, 2, [(2, 2), (5953, 1)]),
  (1476407, 5, [(2, 1), (31, 1), (23813, 1)]),
  (199999997849, 3, [(2, 3), (7, 1), (41, 1), (59, 1), (1476407, 1)]),
  (399999995699, 2, [(2, 1), (199999997849, 1)]),
  (7127, 5, [(2, 1), (7, 1), (509, 1)]),
  (212593, 5, [(2, 4), (3, 1), (43, 1)]),
  (1275559, 3, [(2, 1), (3, 1), (212593, 1)]),
  (399999995693, 2, [(2, 2), (11, 1), (7127, 1), (1275559, 1)]),
  (118273, 5, [(2, 9)]),
  (1691003, 2, [(2, 1), (727, 1)]),
  (399999995639, 17, [(2, 1), (118273, 1), (1691003, 1)]),
  (10789, 2, [(2, 2), (3, 1), (29, 1)]),
  (2059711, 11, [(2, 1), (3, 1), (5, 1), (71, 1)]),
  (399999995623, 3, [(2, 1), (3, 2), (10789, 1), (2059711, 1)]),
  (36781, 2, [(2, 2), (3, 1), (5, 1), (613, 1)]),
  (399999995581, 6, [(2, 2), (3, 1), (5, 1), (36781, 1)]),
  (163398691, 10, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (71, 1)]),
  (399999995569, 7, [(2, 4), (3, 2), (17, 1), (163398691, 1)])]

/-- Kernel acceptance of chunk 15, page 210. -/
theorem chain15 : Big.chainP K15 S15 = true := by decide +kernel

/-- Each entry of chunk 15 is prime, page 210. -/
theorem primes15 : ∀ c ∈ S15, c.1.Prime := by
  apply Big.chainP_sound S15 K15 ?_ chain15
  intro p hp
  have hm : K15.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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

#print axioms chain15
#print axioms primes15

end LeanLab.DtRS1998.Task303.Low
