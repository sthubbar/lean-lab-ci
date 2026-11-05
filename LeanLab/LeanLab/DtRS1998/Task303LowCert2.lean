/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert1

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K2 : List ℕ := [19037]

/-- Pocklington entries for chunk 2, page 210. -/
def S2 : List Big.Cert := [(399999999419, 2, [(2, 1), (271, 1), (19037, 1)]),
  (1031, 14, [(2, 1), (5, 1), (103, 1)]),
  (2063, 5, [(2, 1), (1031, 1)]),
  (4127, 5, [(2, 1), (2063, 1)]),
  (2019223, 3, [(2, 1), (3, 3), (61, 1)]),
  (399999999409, 7, [(2, 4), (3, 1), (4127, 1), (2019223, 1)]),
  (51349, 10, [(2, 2), (3, 1), (11, 1), (389, 1)]),
  (1232377, 7, [(2, 3), (3, 1), (51349, 1)]),
  (177462289, 17, [(2, 4), (3, 2), (1232377, 1)]),
  (399999999407, 5, [(2, 1), (7, 2), (23, 1), (177462289, 1)]),
  (50226017, 3, [(2, 5), (643, 1)]),
  (399999999389, 2, [(2, 2), (11, 1), (181, 1), (50226017, 1)]),
  (2161, 7, [(2, 4), (3, 3)]),
  (12967, 3, [(2, 1), (3, 1), (2161, 1)]),
  (399999999313, 5, [(2, 4), (3, 2), (12967, 1)]),
  (5581, 6, [(2, 2), (3, 2), (5, 1)]),
  (33487, 6, [(2, 1), (3, 1), (5581, 1)]),
  (133949, 2, [(2, 2), (33487, 1)]),
  (267899, 2, [(2, 1), (133949, 1)]),
  (168776371, 2, [(2, 1), (3, 2), (5, 1), (7, 1), (267899, 1)]),
  (399999999271, 3, [(2, 1), (3, 1), (5, 1), (79, 1), (168776371, 1)]),
  (7717, 2, [(2, 2), (3, 1), (643, 1)]),
  (399999999239, 11, [(2, 1), (7, 1), (29, 1), (7717, 1)]),
  (2767, 3, [(2, 1), (3, 1), (461, 1)]),
  (399999999233, 3, [(2, 8), (101, 1), (2767, 1)]),
  (2711, 7, [(2, 1), (5, 1), (271, 1)]),
  (16267, 3, [(2, 1), (3, 1), (2711, 1)]),
  (4391, 14, [(2, 1), (5, 1), (439, 1)]),
  (614741, 2, [(2, 2), (5, 1), (7, 1), (4391, 1)]),
  (1229483, 2, [(2, 1), (614741, 1)])]

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

end LeanLab.DtRS1998.Task303.Low
