/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert0

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K1 : List ℕ := [43394406943]

/-- Pocklington entries for chunk 1, page 210. -/
def S1 : List Big.Cert := [(89999999999783, 5, [(2, 1), (17, 1), (61, 1), (43394406943, 1)]),
  (1283, 2, [(2, 1), (641, 1)]),
  (7699, 3, [(2, 1), (3, 1), (1283, 1)]),
  (89999999999753, 3, [(2, 3), (47, 1), (179, 1), (7699, 1)]),
  (1039, 3, [(2, 1), (3, 1), (173, 1)]),
  (185089213, 2, [(2, 2), (3, 5), (7, 1), (11, 1)]),
  (89999999999677, 2, [(2, 2), (3, 2), (13, 1), (1039, 1), (185089213, 1)]),
  (185753, 3, [(2, 3), (7, 1), (31, 1)]),
  (89999999999647, 5, [(2, 1), (3, 1), (11, 1), (17, 1), (185753, 1)]),
  (3061, 6, [(2, 2), (3, 2), (5, 1)]),
  (104147, 2, [(2, 1), (7, 1), (43, 1)]),
  (89999999999639, 7, [(2, 1), (3061, 1), (104147, 1)]),
  (4441, 13, [(2, 3), (3, 1), (5, 1)]),
  (43517, 2, [(2, 2), (11, 1), (23, 1)]),
  (1566613, 2, [(2, 2), (3, 2), (43517, 1)]),
  (131595493, 2, [(2, 2), (3, 1), (7, 1), (1566613, 1)]),
  (89999999999603, 11, [(2, 1), (7, 1), (11, 1), (4441, 1), (131595493, 1)]),
  (89999999999597, 2, [(2, 2), (79, 1), (283, 1), (647, 1)]),
  (1831, 3, [(2, 1), (3, 1), (5, 1), (61, 1)]),
  (89999999999551, 3, [(2, 1), (3, 2), (5, 2), (251, 1), (1831, 1)]),
  (3756887, 7, [(2, 1), (7, 1), (149, 1)]),
  (89999999999549, 2, [(2, 2), (3756887, 1)]),
  (2617, 5, [(2, 3), (3, 1), (109, 1)]),
  (89999999999501, 3, [(2, 2), (5, 3), (479, 1), (2617, 1)]),
  (10267, 2, [(2, 1), (3, 1), (29, 1)]),
  (61603, 2, [(2, 1), (3, 1), (10267, 1)]),
  (1471, 6, [(2, 1), (3, 1), (5, 1), (7, 2)]),
  (2069, 2, [(2, 2), (11, 1), (47, 1)]),
  (16553, 3, [(2, 3), (2069, 1)]),
  (48698927, 5, [(2, 1), (1471, 1), (16553, 1)])]

/-- Kernel acceptance of chunk 1, page 210. -/
theorem chain1 : Big.chainP K1 S1 = true := by decide +kernel

/-- Each entry of chunk 1 is prime, page 210. -/
theorem primes1 : ∀ c ∈ S1, c.1.Prime := by
  apply Big.chainP_sound S1 K1 ?_ chain1
  intro p hp
  have hm : K1.all (fun p => S0.any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  exact primes0 c hc

#print axioms chain1
#print axioms primes1

end LeanLab.DtRS1998.Task303.High
