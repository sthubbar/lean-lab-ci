/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert3

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K4 : List ℕ := [1783, 6113]

/-- Pocklington entries for chunk 4, page 210. -/
def S4 : List Big.Cert := [(12227, 2, [(2, 1), (6113, 1)]),
  (130804447, 5, [(2, 1), (3, 1), (1783, 1), (12227, 1)]),
  (399999998927, 5, [(2, 1), (11, 1), (139, 1), (130804447, 1)]),
  (16666666619, 6, [(2, 1), (7, 1), (17, 1), (29, 1), (571, 1)]),
  (33333333239, 13, [(2, 1), (16666666619, 1)]),
  (399999998869, 6, [(2, 2), (3, 1), (33333333239, 1)]),
  (99999999709, 2, [(2, 2), (3, 1), (7, 1), (17, 1), (29, 1), (571, 1)]),
  (399999998837, 2, [(2, 2), (99999999709, 1)]),
  (28099, 2, [(2, 1), (3, 2), (7, 1), (223, 1)]),
  (399999998819, 2, [(2, 1), (7, 2), (28099, 1)]),
  (399999998813, 2, [(2, 2), (41, 1), (67, 1), (541, 1)]),
  (399999998791, 3, [(2, 1), (3, 5), (5, 1), (7, 1), (823, 1)]),
  (2417, 3, [(2, 4), (151, 1)]),
  (399999998639, 13, [(2, 1), (37, 1), (79, 1), (2417, 1)]),
  (13399, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]),
  (399999998627, 2, [(2, 1), (101, 1), (13399, 1)]),
  (4729, 17, [(2, 3), (3, 1), (197, 1)]),
  (2950897, 5, [(2, 4), (3, 1), (13, 1), (4729, 1)]),
  (47214353, 3, [(2, 4), (2950897, 1)]),
  (399999998617, 5, [(2, 3), (3, 1), (353, 1), (47214353, 1)]),
  (2113, 5, [(2, 6)]),
  (1319, 13, [(2, 1), (659, 1)]),
  (137177, 3, [(2, 3), (13, 1), (1319, 1)]),
  (4115311, 7, [(2, 1), (3, 1), (5, 1), (137177, 1)]),
  (399999998579, 2, [(2, 1), (23, 1), (2113, 1), (4115311, 1)]),
  (1033, 5, [(2, 3), (3, 1), (43, 1)]),
  (6199, 3, [(2, 1), (3, 1), (1033, 1)]),
  (136379, 6, [(2, 1), (11, 1), (6199, 1)]),
  (272759, 7, [(2, 1), (136379, 1)]),
  (31094527, 3, [(2, 1), (3, 1), (19, 1), (272759, 1)])]

/-- Kernel acceptance of chunk 4, page 210. -/
theorem chain4 : Big.chainP K4 S4 = true := by decide +kernel

/-- Each entry of chunk 4 is prime, page 210. -/
theorem primes4 : ∀ c ∈ S4, c.1.Prime := by
  apply Big.chainP_sound S4 K4 ?_ chain4
  intro p hp
  have hm : K4.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3)))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3

#print axioms chain4
#print axioms primes4

end LeanLab.DtRS1998.Task303.Low
