/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowData

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K0 : List ℕ := []

/-- Pocklington entries for chunk 0, page 210. -/
def S0 : List Big.Cert := [(19009, 23, [(2, 6), (3, 3)]),
  (9133, 6, [(2, 2), (3, 1), (761, 1)]),
  (109597, 5, [(2, 2), (3, 1), (9133, 1)]),
  (657583, 3, [(2, 1), (3, 1), (109597, 1)]),
  (2630333, 2, [(2, 2), (657583, 1)]),
  (399999999977, 3, [(2, 3), (19009, 1), (2630333, 1)]),
  (399999999961, 17, [(2, 3), (3, 2), (5, 1), (11, 1), (41, 1), (271, 1)]),
  (399999999953, 13, [(2, 4), (7, 1), (359, 1), (367, 1)]),
  (5347, 3, [(2, 1), (3, 5)]),
  (32083, 2, [(2, 1), (3, 1), (5347, 1)]),
  (623383, 5, [(2, 1), (3, 1), (107, 1), (971, 1)]),
  (6233831, 7, [(2, 1), (5, 1), (623383, 1)]),
  (399999999947, 2, [(2, 1), (32083, 1), (6233831, 1)]),
  (4447, 3, [(2, 1), (3, 2), (13, 1)]),
  (1138433, 3, [(2, 8), (4447, 1)]),
  (2276867, 2, [(2, 1), (1138433, 1)]),
  (81967213, 2, [(2, 2), (3, 2), (2276867, 1)]),
  (819672131, 6, [(2, 1), (5, 1), (81967213, 1)]),
  (399999999929, 3, [(2, 3), (61, 1), (819672131, 1)]),
  (11657, 3, [(2, 3), (31, 1)]),
  (399999999923, 2, [(2, 1), (151, 1), (11657, 1)]),
  (2857, 11, [(2, 3), (3, 1), (7, 1)]),
  (28571, 2, [(2, 1), (5, 1), (2857, 1)]),
  (399999999911, 7, [(2, 1), (5, 1), (7, 1), (28571, 1)]),
  (727272727, 5, [(2, 1), (3, 1), (83, 1), (577, 1)]),
  (399999999851, 2, [(2, 1), (5, 2), (11, 1), (727272727, 1)]),
  (1861, 2, [(2, 2), (3, 1), (5, 1)]),
  (85607, 5, [(2, 1), (23, 1), (1861, 1)]),
  (1540927, 3, [(2, 1), (3, 2), (85607, 1)]),
  (73964497, 5, [(2, 4), (3, 1), (1540927, 1)])]

/-- Kernel acceptance of chunk 0, page 210. -/
theorem chain0 : Big.chainP K0 S0 = true := by decide +kernel

/-- Each entry of chunk 0 is prime, page 210. -/
theorem primes0 : ∀ c ∈ S0, c.1.Prime := by
  apply Big.chainP_sound S0 K0 ?_ chain0
  simp [K0]

#print axioms chain0
#print axioms primes0

end LeanLab.DtRS1998.Task303.Low
