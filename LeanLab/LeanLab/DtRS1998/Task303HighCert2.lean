/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert1

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K2 : List ℕ := [61603, 48698927]

/-- Pocklington entries for chunk 2, page 210. -/
def S2 : List Big.Cert := [(89999999999431, 13, [(2, 1), (3, 1), (5, 1), (61603, 1), (48698927, 1)]),
  (1063, 3, [(2, 1), (3, 2), (59, 1)]),
  (12757, 2, [(2, 2), (3, 1), (1063, 1)]),
  (12093637, 5, [(2, 2), (3, 1), (79, 1), (12757, 1)]),
  (89999999999411, 2, [(2, 1), (5, 1), (839, 1), (887, 1), (12093637, 1)]),
  (2129, 3, [(2, 4), (7, 1)]),
  (2237, 2, [(2, 2), (13, 1)]),
  (139978039, 3, [(2, 1), (3, 1), (2237, 1)]),
  (89999999999363, 2, [(2, 1), (151, 1), (2129, 1), (139978039, 1)]),
  (4153, 5, [(2, 3), (3, 1), (173, 1)]),
  (75773011, 2, [(2, 1), (3, 1), (5, 1), (479, 1)]),
  (89999999999339, 2, [(2, 1), (11, 1), (13, 1), (4153, 1), (75773011, 1)]),
  (1051, 7, [(2, 1), (3, 1), (5, 2)]),
  (3001, 14, [(2, 3), (3, 1), (5, 3)]),
  (89999999999333, 2, [(2, 2), (19, 1), (1051, 1), (3001, 1)]),
  (3214285714261, 2, [(2, 2), (3, 2), (5, 1), (79, 1), (103, 1), (439, 1)]),
  (89999999999309, 2, [(2, 2), (7, 1), (3214285714261, 1)]),
  (1650528169, 7, [(2, 3), (3, 1), (43, 1), (977, 1)]),
  (1406249999989, 2, [(2, 2), (3, 1), (71, 1), (1650528169, 1)]),
  (89999999999297, 3, [(2, 6), (1406249999989, 1)]),
  (378127, 5, [(2, 1), (3, 2), (7, 1), (3001, 1)]),
  (89999999999291, 2, [(2, 1), (5, 1), (23, 1), (378127, 1)]),
  (20593, 5, [(2, 4), (3, 2)]),
  (44999999999639, 11, [(2, 1), (457, 1), (20593, 1)]),
  (89999999999279, 13, [(2, 1), (44999999999639, 1)]),
  (2411, 6, [(2, 1), (5, 1), (241, 1)]),
  (89999999999227, 2, [(2, 1), (3, 2), (67, 1), (307, 1), (2411, 1)]),
  (2833, 5, [(2, 4), (3, 1), (59, 1)]),
  (3142901, 2, [(2, 2), (5, 2), (53, 1)]),
  (836011667, 2, [(2, 1), (7, 1), (19, 1), (3142901, 1)])]

/-- Kernel acceptance of chunk 2, page 210. -/
theorem chain2 : Big.chainP K2 S2 = true := by decide +kernel

/-- Each entry of chunk 2 is prime, page 210. -/
theorem primes2 : ∀ c ∈ S2, c.1.Prime := by
  apply Big.chainP_sound S2 K2 ?_ chain2
  intro p hp
  have hm : K2.all (fun p => (S0 ++ (S1)).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1
  · exact primes0 c h0
  · exact primes1 c h1

#print axioms chain2
#print axioms primes2

end LeanLab.DtRS1998.Task303.High
