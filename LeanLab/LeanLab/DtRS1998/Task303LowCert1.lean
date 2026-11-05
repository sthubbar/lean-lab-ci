/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert0

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K1 : List ℕ := [73964497]

/-- Pocklington entries for chunk 1, page 210. -/
def S1 : List Big.Cert := [(199999999889, 3, [(2, 4), (13, 2), (73964497, 1)]),
  (399999999779, 2, [(2, 1), (199999999889, 1)]),
  (399999999757, 5, [(2, 2), (3, 1), (7, 1), (211, 1), (223, 1)]),
  (6802721, 3, [(2, 5), (5, 1), (17, 1)]),
  (81632653, 5, [(2, 2), (3, 1), (6802721, 1)]),
  (399999999701, 2, [(2, 2), (5, 2), (7, 2), (81632653, 1)]),
  (333667, 2, [(2, 1), (3, 3), (37, 1)]),
  (6666666661, 2, [(2, 2), (3, 3), (5, 1), (37, 1), (333667, 1)]),
  (399999999661, 6, [(2, 2), (3, 1), (5, 1), (6666666661, 1)]),
  (399999999617, 5, [(2, 7), (7, 1), (67, 1), (293, 1)]),
  (39999999961, 7, [(2, 3), (3, 4), (5, 1), (37, 1), (333667, 1)]),
  (399999999611, 6, [(2, 1), (5, 1), (39999999961, 1)]),
  (399999999601, 19, [(2, 4), (3, 4), (5, 2), (37, 1)]),
  (55469, 2, [(2, 2), (7, 2), (283, 1)]),
  (2329699, 2, [(2, 1), (3, 1), (7, 1), (55469, 1)]),
  (4761904757, 3, [(2, 2), (7, 1), (73, 1), (2329699, 1)]),
  (399999999589, 10, [(2, 2), (3, 1), (7, 1), (4761904757, 1)]),
  (399999999491, 6, [(2, 1), (5, 1), (7, 1), (13, 1), (31, 2)]),
  (11778563, 2, [(2, 1), (41, 1), (379, 2)]),
  (399999999481, 7, [(2, 3), (3, 1), (5, 1), (283, 1), (11778563, 1)]),
  (7164863, 5, [(2, 1), (19, 1), (409, 1)]),
  (14329727, 5, [(2, 1), (7164863, 1)]),
  (399999999479, 11, [(2, 1), (17, 1), (821, 1), (14329727, 1)]),
  (20021, 3, [(2, 2), (5, 1), (7, 1), (11, 1)]),
  (399999999463, 7, [(2, 1), (3, 1), (7, 1), (20021, 1)]),
  (5023, 3, [(2, 1), (3, 4)]),
  (16123831, 3, [(2, 1), (3, 1), (5, 1), (107, 1), (5023, 1)]),
  (399999999449, 3, [(2, 3), (7, 1), (443, 1), (16123831, 1)]),
  (4759, 3, [(2, 1), (3, 1), (13, 1)]),
  (19037, 2, [(2, 2), (4759, 1)])]

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

end LeanLab.DtRS1998.Task303.Low
