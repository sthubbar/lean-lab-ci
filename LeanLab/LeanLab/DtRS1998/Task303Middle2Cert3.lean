/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert2

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K3 : List ℕ := [900461]

/-- Pocklington entries for chunk 3, page 210. -/
def S3 : List Big.Cert := [(41233, 5, [(2, 4), (3, 1), (859, 1)]),
  (8329067, 2, [(2, 1), (101, 1), (41233, 1)]),
  (29999999999549, 2, [(2, 2), (900461, 1), (8329067, 1)]),
  (59999999999099, 2, [(2, 1), (29999999999549, 1)]),
  (1013, 3, [(2, 2), (11, 1)]),
  (20261, 2, [(2, 2), (5, 1), (1013, 1)]),
  (11132911, 6, [(2, 1), (3, 3), (5, 1), (41233, 1)]),
  (59999999999087, 5, [(2, 1), (7, 1), (19, 1), (20261, 1), (11132911, 1)]),
  (59999999999077, 2, [(2, 2), (3, 3), (379, 2)]),
  (6529, 7, [(2, 7)]),
  (25253, 2, [(2, 2), (59, 1)]),
  (59999999998997, 2, [(2, 2), (6529, 1), (25253, 1)]),
  (2311, 3, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (135222847, 5, [(2, 1), (3, 1), (11, 1), (659, 1)]),
  (540891389, 2, [(2, 2), (135222847, 1)]),
  (59999999998993, 7, [(2, 4), (3, 1), (2311, 1), (540891389, 1)]),
  (4783, 6, [(2, 1), (3, 1), (797, 1)]),
  (57397, 2, [(2, 2), (3, 1), (4783, 1)]),
  (918353, 3, [(2, 4), (57397, 1)]),
  (1814843, 2, [(2, 1), (19, 1), (163, 1)]),
  (10889059, 10, [(2, 1), (3, 1), (1814843, 1)]),
  (59999999998963, 2, [(2, 1), (3, 1), (918353, 1), (10889059, 1)]),
  (19813, 2, [(2, 2), (3, 1), (13, 1)]),
  (6023153, 3, [(2, 4), (19, 1), (19813, 1)]),
  (285714285709, 2, [(2, 2), (3, 1), (59, 1), (67, 1), (6023153, 1)]),
  (59999999998891, 2, [(2, 1), (3, 1), (5, 1), (7, 1), (285714285709, 1)]),
  (230339, 2, [(2, 1), (41, 1), (53, 2)]),
  (6313131313, 7, [(2, 4), (3, 1), (571, 1), (230339, 1)]),
  (833333333317, 2, [(2, 2), (3, 1), (11, 1), (6313131313, 1)]),
  (4999999999903, 3, [(2, 1), (3, 1), (833333333317, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle2
