/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert4

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K5 : List ℕ := [31094527]

/-- Pocklington entries for chunk 5, page 210. -/
def S5 : List Big.Cert := [(124378109, 2, [(2, 2), (31094527, 1)]),
  (16666666607, 5, [(2, 1), (67, 1), (124378109, 1)]),
  (399999998569, 7, [(2, 3), (3, 1), (16666666607, 1)]),
  (399999998561, 6, [(2, 5), (5, 1), (17, 2), (31, 1)]),
  (1823, 5, [(2, 1), (911, 1)]),
  (4889, 3, [(2, 3), (13, 1)]),
  (997357, 5, [(2, 2), (3, 1), (17, 1), (4889, 1)]),
  (199999999211, 2, [(2, 1), (5, 1), (11, 1), (1823, 1), (997357, 1)]),
  (399999998423, 5, [(2, 1), (199999999211, 1)]),
  (29443, 2, [(2, 1), (3, 1), (7, 1), (701, 1)]),
  (199800199, 6, [(2, 1), (3, 2), (13, 1), (29, 1), (29443, 1)]),
  (399999998399, 7, [(2, 1), (7, 1), (11, 1), (13, 1), (199800199, 1)]),
  (1297, 10, [(2, 4), (3, 4)]),
  (1723, 3, [(2, 1), (3, 1), (7, 1)]),
  (389399, 17, [(2, 1), (113, 1), (1723, 1)]),
  (66666666397, 2, [(2, 2), (3, 1), (11, 1), (1297, 1), (389399, 1)]),
  (399999998383, 3, [(2, 1), (3, 1), (66666666397, 1)]),
  (431034481, 14, [(2, 4), (3, 3), (5, 1), (431, 1)]),
  (399999998369, 3, [(2, 5), (29, 1), (431034481, 1)]),
  (619763, 2, [(2, 1), (11, 2), (13, 1)]),
  (8333333299, 2, [(2, 1), (3, 4), (83, 1), (619763, 1)]),
  (399999998353, 5, [(2, 4), (3, 1), (8333333299, 1)]),
  (764947, 3, [(2, 1), (3, 2), (7, 1), (13, 1)]),
  (12239153, 3, [(2, 4), (764947, 1)]),
  (399999998347, 5, [(2, 1), (3, 1), (13, 1), (419, 1), (12239153, 1)]),
  (2647, 3, [(2, 1), (3, 3)]),
  (174703, 3, [(2, 1), (3, 1), (11, 1), (2647, 1)]),
  (41928721, 19, [(2, 4), (3, 1), (5, 1), (174703, 1)]),
  (399999998341, 6, [(2, 2), (3, 2), (5, 1), (53, 1), (41928721, 1)]),
  (1427, 2, [(2, 1), (23, 1)])]

/-- Kernel acceptance of chunk 5, page 210. -/
theorem chain5 : Big.chainP K5 S5 = true := by decide +kernel

/-- Each entry of chunk 5 is prime, page 210. -/
theorem primes5 : ∀ c ∈ S5, c.1.Prime := by
  apply Big.chainP_sound S5 K5 ?_ chain5
  intro p hp
  have hm : K5.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4

#print axioms chain5
#print axioms primes5

end LeanLab.DtRS1998.Task303.Low
