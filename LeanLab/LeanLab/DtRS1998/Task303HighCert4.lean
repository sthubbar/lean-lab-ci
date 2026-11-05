/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert3

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K4 : List ℕ := [152879, 21025031]

/-- Pocklington entries for chunk 4, page 210. -/
def S4 : List Big.Cert := [(89999999998973, 2, [(2, 2), (7, 1), (152879, 1), (21025031, 1)]),
  (52571, 2, [(2, 1), (5, 1), (7, 1), (751, 1)]),
  (89999999998939, 3, [(2, 1), (3, 7), (52571, 1)]),
  (62423, 5, [(2, 1), (23, 2)]),
  (124847, 5, [(2, 1), (62423, 1)]),
  (89999999998921, 14, [(2, 3), (3, 2), (5, 1), (11, 1), (124847, 1)]),
  (270749, 2, [(2, 2), (113, 1), (599, 1)]),
  (8910891089, 6, [(2, 4), (11, 2), (17, 1), (270749, 1)]),
  (89999999998901, 2, [(2, 2), (5, 2), (101, 1), (8910891089, 1)]),
  (92461, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]),
  (2228495023, 21, [(2, 1), (3, 2), (13, 1), (103, 1), (92461, 1)]),
  (89999999998879, 3, [(2, 1), (3, 1), (53, 1), (127, 1), (2228495023, 1)]),
  (8297, 3, [(2, 3), (17, 1)]),
  (116159, 7, [(2, 1), (7, 1), (8297, 1)]),
  (23231801, 7, [(2, 3), (5, 2), (116159, 1)]),
  (46463603, 2, [(2, 1), (23231801, 1)]),
  (92927207, 5, [(2, 1), (46463603, 1)]),
  (4646360351, 37, [(2, 1), (5, 2), (92927207, 1)]),
  (89999999998871, 14, [(2, 1), (5, 1), (13, 1), (149, 1), (4646360351, 1)]),
  (1693, 2, [(2, 2), (3, 2), (47, 1)]),
  (16931, 2, [(2, 1), (5, 1), (1693, 1)]),
  (135449, 3, [(2, 3), (16931, 1)]),
  (270899, 2, [(2, 1), (135449, 1)]),
  (89999999998861, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (270899, 1)]),
  (1709, 3, [(2, 2), (7, 1), (61, 1)]),
  (434087, 5, [(2, 1), (127, 1), (1709, 1)]),
  (89999999998771, 3, [(2, 1), (3, 1), (5, 1), (434087, 1)]),
  (474969127, 3, [(2, 1), (3, 1), (71, 1), (967, 1)]),
  (89999999998723, 2, [(2, 1), (3, 3), (11, 2), (29, 1), (474969127, 1)]),
  (87481, 29, [(2, 3), (3, 7)])]

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

end LeanLab.DtRS1998.Task303.High
