/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert2

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K3 : List ℕ := [1031, 16267, 1229483]

/-- Pocklington entries for chunk 3, page 210. -/
def S3 : List Big.Cert := [(399999999221, 3, [(2, 2), (5, 1), (16267, 1), (1229483, 1)]),
  (399999999169, 17, [(2, 6), (3, 3), (7, 1), (11, 1), (751, 1)]),
  (13619, 2, [(2, 1), (11, 1), (619, 1)]),
  (399999999109, 2, [(2, 2), (3, 1), (19, 1), (13619, 1)]),
  (23668639, 3, [(2, 1), (3, 1), (7, 1), (653, 1)]),
  (399999999101, 2, [(2, 2), (5, 2), (13, 2), (23668639, 1)]),
  (5851, 2, [(2, 1), (3, 2), (5, 2)]),
  (399999999083, 2, [(2, 1), (37, 1), (53, 1), (5851, 1)]),
  (399999999073, 5, [(2, 5), (3, 1), (263, 1), (827, 1)]),
  (399999999067, 7, [(2, 1), (3, 1), (47, 1), (73, 1), (971, 1)]),
  (6377551, 11, [(2, 1), (3, 1), (5, 2), (17, 1)]),
  (1249999997, 3, [(2, 2), (7, 2), (6377551, 1)]),
  (399999999041, 3, [(2, 6), (5, 1), (1249999997, 1)]),
  (11783, 5, [(2, 1), (43, 1), (137, 1)]),
  (652831, 3, [(2, 1), (3, 1), (5, 1), (47, 1)]),
  (15384615347, 2, [(2, 1), (11783, 1), (652831, 1)]),
  (399999999023, 5, [(2, 1), (13, 1), (15384615347, 1)]),
  (33331, 3, [(2, 1), (3, 1), (5, 1), (11, 1)]),
  (412371133, 2, [(2, 2), (3, 1), (1031, 1), (33331, 1)]),
  (399999999011, 2, [(2, 1), (5, 1), (97, 1), (412371133, 1)]),
  (199999999499, 2, [(2, 1), (13, 1), (11783, 1), (652831, 1)]),
  (399999998999, 17, [(2, 1), (199999999499, 1)]),
  (1201, 11, [(2, 4), (3, 1)]),
  (699697, 7, [(2, 4), (3, 2), (43, 1)]),
  (23789699, 2, [(2, 1), (17, 1), (699697, 1)]),
  (399999998987, 2, [(2, 1), (7, 1), (1201, 1), (23789699, 1)]),
  (3225806443, 2, [(2, 1), (3, 2), (23, 1), (719, 1)]),
  (399999998933, 2, [(2, 2), (31, 1), (3225806443, 1)]),
  (1783, 5, [(2, 1), (3, 4)]),
  (6113, 3, [(2, 5), (191, 1)])]

/-- Kernel acceptance of chunk 3, page 210. -/
theorem chain3 : Big.chainP K3 S3 = true := by decide +kernel

/-- Each entry of chunk 3 is prime, page 210. -/
theorem primes3 : ∀ c ∈ S3, c.1.Prime := by
  apply Big.chainP_sound S3 K3 ?_ chain3
  intro p hp
  have hm : K3.all (fun p => (S0 ++ (S1 ++ (S2))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2

#print axioms chain3
#print axioms primes3

end LeanLab.DtRS1998.Task303.Low
