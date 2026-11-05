/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert7

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K8 : List ℕ := [1033, 1231, 1540927]

/-- Pocklington entries for chunk 8, page 210. -/
def S8 : List Big.Cert := [(399999997751, 7, [(2, 1), (5, 3), (23, 1), (37, 1), (47, 1)]),
  (1388888881, 22, [(2, 4), (3, 1), (5, 1), (29, 1), (431, 1)]),
  (399999997729, 7, [(2, 5), (3, 2), (1388888881, 1)]),
  (24793, 5, [(2, 3), (3, 1), (1033, 1)]),
  (399999997699, 2, [(2, 1), (3, 1), (7, 1), (24793, 1)]),
  (120192307, 3, [(2, 1), (3, 1), (13, 1), (1540927, 1)]),
  (399999997697, 3, [(2, 8), (13, 1), (120192307, 1)]),
  (10069, 2, [(2, 2), (3, 1), (839, 1)]),
  (40277, 2, [(2, 2), (10069, 1)]),
  (4591579, 2, [(2, 1), (3, 1), (19, 1), (40277, 1)]),
  (266311583, 5, [(2, 1), (29, 1), (4591579, 1)]),
  (399999997667, 2, [(2, 1), (751, 1), (266311583, 1)]),
  (399999997633, 7, [(2, 6), (3, 1), (313, 1), (1231, 1)]),
  (1051, 7, [(2, 1), (3, 1), (5, 2)]),
  (278209, 11, [(2, 6), (3, 3)]),
  (3508771909, 6, [(2, 2), (3, 1), (1051, 1), (278209, 1)]),
  (399999997627, 3, [(2, 1), (3, 1), (19, 1), (3508771909, 1)]),
  (9100009, 11, [(2, 3), (3, 2), (211, 1)]),
  (200200199, 11, [(2, 1), (11, 1), (9100009, 1)]),
  (399999997603, 2, [(2, 1), (3, 3), (37, 1), (200200199, 1)]),
  (27251669, 2, [(2, 2), (131, 2)]),
  (399999997583, 5, [(2, 1), (41, 1), (179, 1), (27251669, 1)]),
  (381679387, 5, [(2, 1), (3, 1), (11, 1), (47, 1), (71, 1)]),
  (399999997577, 3, [(2, 3), (131, 1), (381679387, 1)]),
  (1223, 5, [(2, 1), (13, 1), (47, 1)]),
  (721571, 2, [(2, 1), (5, 1), (59, 1), (1223, 1)]),
  (399999997567, 3, [(2, 1), (3, 2), (13, 1), (23, 1), (103, 1), (721571, 1)]),
  (13099, 3, [(2, 1), (3, 1), (37, 1)]),
  (399999997519, 3, [(2, 1), (3, 1), (11, 1), (13099, 1)]),
  (1601, 3, [(2, 6)])]

/-- Kernel acceptance of chunk 8, page 210. -/
theorem chain8 : Big.chainP K8 S8 = true := by decide +kernel

/-- Each entry of chunk 8 is prime, page 210. -/
theorem primes8 : ∀ c ∈ S8, c.1.Prime := by
  apply Big.chainP_sound S8 K8 ?_ chain8
  intro p hp
  have hm : K8.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7)))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7

#print axioms chain8
#print axioms primes8

end LeanLab.DtRS1998.Task303.Low
