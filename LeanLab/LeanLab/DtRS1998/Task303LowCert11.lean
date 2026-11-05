/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert10

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K11 : List ℕ := [4363, 29443, 267899, 2276867]

/-- Pocklington entries for chunk 11, page 210. -/
def S11 : List Big.Cert := [(399999997069, 2, [(2, 2), (3, 1), (7, 1), (53, 1), (4363, 1)]),
  (7572889, 19, [(2, 3), (3, 2), (17, 1), (23, 1)]),
  (199999998491, 2, [(2, 1), (5, 1), (19, 1), (139, 1), (7572889, 1)]),
  (399999996983, 5, [(2, 1), (199999998491, 1)]),
  (5714285671, 3, [(2, 1), (3, 3), (5, 1), (79, 1), (267899, 1)]),
  (399999996971, 2, [(2, 1), (5, 1), (7, 1), (5714285671, 1)]),
  (21313, 5, [(2, 6), (3, 2)]),
  (1172993, 3, [(2, 9), (29, 1)]),
  (49999999619, 2, [(2, 1), (21313, 1), (1172993, 1)]),
  (399999996953, 3, [(2, 3), (49999999619, 1)]),
  (766283519, 7, [(2, 1), (7, 1), (11, 1), (13, 2), (29443, 1)]),
  (399999996919, 6, [(2, 1), (3, 2), (29, 1), (766283519, 1)]),
  (399999996901, 6, [(2, 2), (3, 3), (5, 2), (7, 1), (79, 1)]),
  (454545451, 2, [(2, 1), (3, 2), (5, 2), (73, 1)]),
  (399999996881, 3, [(2, 4), (5, 1), (11, 1), (454545451, 1)]),
  (237073, 15, [(2, 4), (3, 1), (11, 1)]),
  (15384615263, 5, [(2, 1), (71, 1), (457, 1), (237073, 1)]),
  (399999996839, 7, [(2, 1), (13, 1), (15384615263, 1)]),
  (1321, 13, [(2, 3), (3, 1), (5, 1)]),
  (399999996827, 2, [(2, 1), (17, 2), (1321, 1)]),
  (182149361, 3, [(2, 4), (5, 1), (2276867, 1)]),
  (399999996757, 6, [(2, 2), (3, 2), (61, 1), (182149361, 1)]),
  (15976993, 10, [(2, 5), (3, 1), (47, 1)]),
  (399999996749, 2, [(2, 2), (11, 1), (569, 1), (15976993, 1)]),
  (5897, 3, [(2, 3), (11, 1)]),
  (399999996701, 2, [(2, 2), (5, 2), (31, 1), (5897, 1)]),
  (6056201, 6, [(2, 3), (5, 2), (107, 1)]),
  (12112403, 2, [(2, 1), (6056201, 1)]),
  (66666666113, 3, [(2, 7), (43, 1), (12112403, 1)]),
  (399999996679, 3, [(2, 1), (3, 1), (66666666113, 1)])]

/-- Kernel acceptance of chunk 11, page 210. -/
theorem chain11 : Big.chainP K11 S11 = true := by decide +kernel

/-- Each entry of chunk 11 is prime, page 210. -/
theorem primes11 : ∀ c ∈ S11, c.1.Prime := by
  apply Big.chainP_sound S11 K11 ?_ chain11
  intro p hp
  have hm : K11.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
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

#print axioms chain11
#print axioms primes11

end LeanLab.DtRS1998.Task303.Low
