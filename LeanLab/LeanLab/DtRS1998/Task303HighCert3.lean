/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert2

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K3 : List ℕ := [2617, 2833, 836011667]

/-- Pocklington entries for chunk 3, page 210. -/
def S3 : List Big.Cert := [(89999999999219, 2, [(2, 1), (19, 1), (2833, 1), (836011667, 1)]),
  (7477, 2, [(2, 2), (3, 1), (7, 1), (89, 1)]),
  (32051282051, 2, [(2, 1), (5, 2), (7477, 1)]),
  (89999999999209, 17, [(2, 3), (3, 3), (13, 1), (32051282051, 1)]),
  (3095809, 7, [(2, 8), (3, 1), (29, 1)]),
  (30958091, 2, [(2, 1), (5, 1), (3095809, 1)]),
  (89999999999197, 2, [(2, 2), (3, 1), (7, 1), (53, 1), (653, 1), (30958091, 1)]),
  (1350373, 2, [(2, 2), (3, 1), (43, 1), (2617, 1)]),
  (76142131979, 2, [(2, 1), (11, 2), (233, 1), (1350373, 1)]),
  (89999999999179, 3, [(2, 1), (3, 1), (197, 1), (76142131979, 1)]),
  (4889, 3, [(2, 3), (13, 1)]),
  (89999999999171, 2, [(2, 1), (5, 1), (17, 1), (37, 1), (4889, 1)]),
  (22073, 3, [(2, 3), (31, 1)]),
  (1571, 2, [(2, 1), (5, 1), (157, 1)]),
  (28279, 3, [(2, 1), (3, 2), (1571, 1)]),
  (15214103, 5, [(2, 1), (269, 1), (28279, 1)]),
  (89999999999093, 2, [(2, 2), (67, 1), (22073, 1), (15214103, 1)]),
  (1877, 2, [(2, 2), (7, 1), (67, 1)]),
  (18130539887, 5, [(2, 1), (107, 1), (1877, 1)]),
  (89999999999069, 2, [(2, 2), (17, 1), (73, 1), (18130539887, 1)]),
  (1291, 2, [(2, 1), (3, 1), (5, 1), (43, 1)]),
  (1013, 3, [(2, 2), (11, 1)]),
  (20261, 2, [(2, 2), (5, 1), (1013, 1)]),
  (4357087529, 3, [(2, 3), (20261, 1)]),
  (11249999999879, 7, [(2, 1), (1291, 1), (4357087529, 1)]),
  (89999999999033, 3, [(2, 3), (11249999999879, 1)]),
  (6949, 2, [(2, 2), (3, 2), (193, 1)]),
  (152879, 11, [(2, 1), (11, 1), (6949, 1)]),
  (161731, 2, [(2, 1), (3, 3), (5, 1), (599, 1)]),
  (21025031, 11, [(2, 1), (5, 1), (13, 1), (161731, 1)])]

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

end LeanLab.DtRS1998.Task303.High
