/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert7

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K8 : List ℕ := [1901]

/-- Pocklington entries for chunk 8, page 210. -/
def S8 : List Big.Cert := [(2749, 6, [(2, 2), (3, 1), (229, 1)]),
  (89999999997619, 14, [(2, 1), (3, 1), (67, 1), (1901, 1), (2749, 1)]),
  (30773, 3, [(2, 2), (7, 2)]),
  (430823, 5, [(2, 1), (7, 1), (30773, 1)]),
  (861647, 5, [(2, 1), (430823, 1)]),
  (15509647, 17, [(2, 1), (3, 2), (861647, 1)]),
  (2999999999917, 11, [(2, 2), (3, 5), (199, 1), (15509647, 1)]),
  (89999999997511, 7, [(2, 1), (3, 1), (5, 1), (2999999999917, 1)]),
  (3557, 2, [(2, 2), (7, 1), (127, 1)]),
  (30269, 3, [(2, 2), (7, 1), (23, 1)]),
  (39289163, 2, [(2, 1), (11, 1), (59, 1), (30269, 1)]),
  (44999999998703, 5, [(2, 1), (7, 1), (23, 1), (3557, 1), (39289163, 1)]),
  (89999999997407, 5, [(2, 1), (44999999998703, 1)]),
  (1229, 2, [(2, 2), (307, 1)]),
  (2459, 2, [(2, 1), (1229, 1)]),
  (855733, 6, [(2, 2), (3, 1), (29, 1), (2459, 1)]),
  (2628811777, 10, [(2, 10), (3, 1), (855733, 1)]),
  (89999999997373, 5, [(2, 2), (3, 3), (317, 1), (2628811777, 1)]),
  (1753, 7, [(2, 3), (3, 1), (73, 1)]),
  (374999999989, 2, [(2, 2), (3, 1), (47, 1), (1753, 1)]),
  (14999999999561, 6, [(2, 3), (5, 1), (374999999989, 1)]),
  (89999999997367, 3, [(2, 1), (3, 1), (14999999999561, 1)]),
  (3329, 3, [(2, 8)]),
  (239689, 11, [(2, 3), (3, 2), (3329, 1)]),
  (2346791, 13, [(2, 1), (5, 1), (331, 1)]),
  (46935821, 3, [(2, 2), (5, 1), (2346791, 1)]),
  (89999999997353, 3, [(2, 3), (239689, 1), (46935821, 1)]),
  (7673942701, 2, [(2, 2), (3, 3), (5, 2), (71, 1)]),
  (89999999997329, 3, [(2, 4), (733, 1), (7673942701, 1)]),
  (749999999977, 5, [(2, 3), (3, 1), (47, 1), (1753, 1)])]

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

end LeanLab.DtRS1998.Task303.High
