/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert3

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K4 : List ℕ := [4999999999903]

/-- Pocklington entries for chunk 4, page 210. -/
def S4 : List Big.Cert := [(59999999998837, 5, [(2, 2), (3, 1), (4999999999903, 1)]),
  (28037383177, 5, [(2, 3), (3, 1), (11, 1), (661, 1)]),
  (59999999998781, 2, [(2, 2), (5, 1), (107, 1), (28037383177, 1)]),
  (1877, 2, [(2, 2), (7, 1), (67, 1)]),
  (112621, 2, [(2, 2), (3, 1), (5, 1), (1877, 1)]),
  (59999999998721, 3, [(2, 8), (5, 1), (112621, 1)]),
  (2521, 17, [(2, 3), (3, 2)]),
  (3398309, 2, [(2, 2), (337, 1), (2521, 1)]),
  (2732240437, 2, [(2, 2), (3, 1), (67, 1), (3398309, 1)]),
  (27322404371, 10, [(2, 1), (5, 1), (2732240437, 1)]),
  (59999999998717, 2, [(2, 2), (3, 2), (61, 1), (27322404371, 1)]),
  (1181, 7, [(2, 2), (5, 1), (59, 1)]),
  (12893, 3, [(2, 2), (11, 1), (293, 1)]),
  (91359799, 3, [(2, 1), (3, 1), (1181, 1), (12893, 1)]),
  (365439197, 2, [(2, 2), (91359799, 1)]),
  (59999999998643, 2, [(2, 1), (11, 1), (17, 1), (439, 1), (365439197, 1)]),
  (1409, 3, [(2, 7)]),
  (11273, 3, [(2, 3), (1409, 1)]),
  (127747, 2, [(2, 1), (3, 2), (47, 1)]),
  (6131857, 5, [(2, 4), (3, 1), (127747, 1)]),
  (138248847923, 2, [(2, 1), (11273, 1), (6131857, 1)]),
  (59999999998583, 5, [(2, 1), (7, 1), (31, 1), (138248847923, 1)]),
  (1171, 2, [(2, 1), (3, 2), (5, 1)]),
  (23321, 3, [(2, 3), (5, 1), (11, 1)]),
  (46643, 2, [(2, 1), (23321, 1)]),
  (93287, 5, [(2, 1), (46643, 1)]),
  (59999999998559, 11, [(2, 1), (1171, 1), (93287, 1)]),
  (104381, 2, [(2, 2), (5, 1), (17, 1)]),
  (59999999998537, 5, [(2, 3), (3, 3), (13, 1), (104381, 1)]),
  (1697, 3, [(2, 5), (53, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle2
